import logging
from typing import Union
import os
import re
import random
import struct
from six.moves import cStringIO
from pysmt.shortcuts import is_sat, Not, And, TRUE
import pysmt.environment
from pysmt.smtlib.parser import SmtLibParser
from pysmt.typing import BV32, BV8, ArrayType
from pysmt.shortcuts import write_smtlib, get_model, Symbol
from main.utilities import execute_command
from main import emitter, values, reader, parallel, definitions, extractor, oracle
import numpy


logger = logging.getLogger(__name__)
Formula = Union[pysmt.fnode.FNode]
File_Log_Path = "/tmp/log_sym_path"
File_Ktest_Path = "/tmp/concolic.ktest"

list_path_explored = list()
list_path_observed = list()
list_path_detected = list()
count_discovered = 0


def z3_get_model(formula):
    """
           This function will invoke PySMT APIs to solve the provided formula and return the byte list of the model
           Arguments:
               formula: smtlib formatted formula
    """
    emitter.normal("\textracting z3 model")
    model = get_model(formula)
    if model is None:
        return None
    path_script = "/tmp/z3_script"
    write_smtlib(formula, path_script)
    with open(path_script, "r") as script_file:
        script_lines = script_file.readlines()
    script = "".join(script_lines)
    var_list = set(re.findall("\(declare-fun (.+?) \(\)", script))
    sym_var_list = dict()
    for var_name in var_list:
        # sym_var_list[var_name] = dict()
        sym_def = Symbol(var_name, ArrayType(BV32, BV8))
        if sym_def not in model:
            continue
        x = model[sym_def].simplify()
        byte_list = dict()
        value_array_map = x.array_value_assigned_values_map()
        default_value = int(str(x.array_value_default()).split("_")[0])
        if not value_array_map:
            byte_list[0] = default_value
        else:
            for idx, val in value_array_map.items():
                index = int(str(idx).split("_")[0])
                value = int(str(val).split("_")[0])
                byte_list[index] = value

            max_index = max(list(byte_list.keys()))
            if var_name in values.LIST_BIT_LENGTH:
                array_size = values.LIST_BIT_LENGTH[var_name] - 1
                if var_name in ["A-data"]:
                    array_size = max_index

            else:
                array_size = max_index + 1  # TODO: this could be wrong calculation

            if max_index == 0:
                array_size = 2

            if var_name not in ["A-data"]:
                for i in range(0, array_size):
                    if i not in byte_list:
                        byte_list[i] = default_value

            if var_name not in ["A-data", "A-data-stat"]:
                for i in range(array_size - 1, -1, -1):
                    if byte_list[i] == 0:
                        byte_list.pop(i)
                    else:
                        break
        sym_var_list[var_name] = byte_list
    emitter.debug("model var list", sym_var_list)
    return sym_var_list


def z3_get_model_cli(formula):
    """
           This function will invoke the Z3 Cli interface to solve the provided formula and return the model byte list
           Arguments:
               formula: smtlib formatted formula
    """
    emitter.normal("\textracting z3 model")
    path_script = "/tmp/z3_script"
    path_result = "/tmp/z3_output"
    write_smtlib(formula, path_script)
    with open(path_script, "a") as script_file:
        script_file.writelines(["(get-model)\n", "(exit)\n"])
    z3_command = "z3 " + path_script + " > " + path_result
    execute_command(z3_command)
    with open(path_result, "r") as result_file:
        z3_output = result_file.readlines()

    model_byte_list = parse_z3_output(z3_output)
    return model_byte_list


def parse_z3_output(z3_output):
    """
           This function will read the output log of z3 cli interface and extract/parse the values of the model
           Arguments:
               z3_output: string output of the z3 cli invocation
    """
    model = dict()
    var_name = ""
    byte_list = dict()
    str_lambda = ""
    for line in z3_output:
        if "sat" in line or "model" in line:
            continue
        if "define-fun " in line or line == z3_output[-1]:
            if str_lambda:
                if "const" in str_lambda:
                    str_value = str_lambda.split("#x")[-1].split(")")[0]
                    byte_list = dict()
                    byte_list[0] = int("0x" + str_value, 16)
                elif "(lambda ((x!1 (_ BitVec 32))) #x" in str_lambda:
                    str_value = str_lambda.replace("(lambda ((x!1 (_ BitVec 32))) ", "").replace("))", "").replace("\n",
                                                                                                                   "")
                    byte_list[0] = int(str_value.replace("#", "0"), 16)
                elif "true)" in str_lambda:
                    byte_list[0] = int("0xff", 16)
                elif "false)" in str_lambda:
                    byte_list[0] = int("0x00", 16)
                elif "ite" in str_lambda:
                    max_index = 0
                    byte_list = dict()
                    token_list = str_lambda.split("(ite (= x!1 ")
                    for token in token_list[1:]:
                        if token.count("#x") == 2:
                            index, value = token.split(") ")
                        elif token.count("#x") == 3:
                            index, value, default = token.split(" ")
                            index = index.replace(")", "")
                            default = default.split(")")[0].replace("#", "0")
                        index = index.replace("#", "0")
                        value = value.replace("#", "0")
                        index = int(index, 16)
                        if index > max_index:
                            max_index = index
                        byte_list[index] = int(value, 16)

                    if max_index > 0:
                        byte_list.pop(max_index)
                        max_index = max_index - 1

                    for i in range(0, max_index):
                        if i not in byte_list:
                            byte_list[i] = int(default, 16)

                else:
                    print("Unhandled output")
                    print(str_lambda)
                    print(z3_output)
                    exit(1)

            if var_name and byte_list:
                model[var_name] = byte_list
                var_name = ""
                byte_list = dict()
            if line != z3_output[-1]:
                var_name = line.split("define-fun ")[1].split(" ()")[0]
                str_lambda = ""

        else:
            str_lambda += line

    return model


def generate_formula(ppc):
    parser = SmtLibParser()
    script = parser.get_script(cStringIO(ppc))
    formula = script.get_last_formula()
    return formula


def generate_symbolic_paths(ppc_list):
    """
       This function will analyse the partial path conditions collected at each branch location and isolate
       the branch conditions added at each location, negate the constraint to create a new path
              ppc_list : a dictionary containing the partial path condition at each branch location
              returns a list of new partial path conditions
    """
    emitter.normal("\tgenerating new paths")
    path_list = list()
    path_count = 0
    result_list = parallel.generate_symbolic_paths_parallel(ppc_list)
    for result in result_list:
        if result[0]:
            path_count = path_count + 1
            path_list.append((result[1], result[2], result[3]))

    emitter.highlight("\t\tgenerated " + str(path_count) + " flipped path(s)")
    return path_list


# def generate_new_symbolic_paths(constraint_list):
#     """
#     This function will generate N number of new paths by negating each branch condition at a given branch location
#            constraint_list : a dictionary containing the constraints at each branch location
#     """
#     new_path_list = dict()
#     for chosen_control_loc in constraint_list:
#         chosen_constraint_list_at_loc = constraint_list[chosen_control_loc]
#         for chosen_constraint in chosen_constraint_list_at_loc:
#
#     if check_path_feasibility(new_path):
#         if chosen_control_loc not in new_path_list:
#             new_path_list[chosen_control_loc] = set()
#         new_path_list[chosen_control_loc].add(new_path)
#     return new_path_list


def get_signed_value(bit_vector):
    """
      This function will generate the signed value for a given bit list
             bit_vector : list of bits
    """
    signed_value = 0
    for i in sorted(bit_vector.keys()):
        if i == 0:
            signed_value = int(bit_vector[i])
        else:
            signed_value += ((2 << 7) << (int(i) - 1)) * int(bit_vector[i])
    return signed_value


def get_str_value(bit_vector):
    """
      This function will generate the string value for a given bit list
             bit_vector : list of bits
    """
    str_value = ""
    char_list = dict()
    # print(bit_vector)
    for i in bit_vector:
        if int(bit_vector[i]) not in range(32, 127):
            char_list[i] = chr(random.randint(33, 122))
        else:
            char_list[i] = chr(bit_vector[i])
    # print(char_list)
    for i in sorted(char_list):
        char = char_list[i]
        str_value += char
    return str_value


def get_byte_string(bit_vector):
    """
      This function will generate the byte string for a given bit list
             bit_vector : list of bits
    """
    str_value = ""
    char_list = dict()
    # print(bit_vector)
    for i in bit_vector:
        char_list[i] = chr(bit_vector[i])
    # print(char_list)
    for i in sorted(char_list, reverse=True):
        char = char_list[i]
        str_value += char
    return str_value


def select_nearest_control_loc():
    selection = None
    control_loc_list = numpy.array(list_path_detected)[:, 0]
    control_loc_dist_map = dict(
        filter(lambda elem: elem[0] in control_loc_list, values.MAP_LOC_DISTANCE.items()))
    min_distance = min(list(control_loc_dist_map.values()))
    loc_list = list(dict(filter(lambda elem: elem[1] == min_distance, control_loc_dist_map.items())).keys())
    if values.CONF_SELECTION_STRATEGY == "deterministic":
        selection = list(set(loc_list) & set(control_loc_list))[0]
    else:
        selection = random.choice(list(set(loc_list) & set(control_loc_list)))
    return selection


def select_new_path_condition():
    global list_path_detected
    if values.CONF_DISTANCE_METRIC == values.OPTIONS_DIST_METRIC[0]:
        path_list_at_patch_loc = [(p[1], p[2]) for p in list_path_detected if p[0] == values.CONF_LOC_PATCH]
        if path_list_at_patch_loc:
            control_loc = values.CONF_LOC_PATCH
            selected_pair = (max(path_list_at_patch_loc, key=lambda item: item[1]))
            selected_path = selected_pair[0]
            selected_pair = (values.CONF_LOC_PATCH, selected_pair[0], selected_pair[1])
        else:
            selected_pair = max(list_path_detected, key=lambda item: item[2])
            selected_path = selected_pair[1]
            control_loc = selected_pair[0]
        list_path_detected.remove(selected_pair)
    else:
        control_loc = select_nearest_control_loc()
        path_list_at_loc = [(p[1], p[2]) for p in list_path_detected if p[0] == control_loc]
        if values.CONF_SELECTION_STRATEGY == "deterministic":
            selected_pair = (max(path_list_at_loc, key=lambda item: item[1]))
            selected_path = selected_pair[0]
            selected_pair = (control_loc, selected_pair[0], selected_pair[1])
        else:
            selected_pair = (random.choice(path_list_at_loc))
            selected_path = selected_pair[1]
            control_loc = selected_pair[0]
            selected_pair = (control_loc, selected_pair[0], selected_pair[1])
        list_path_detected.remove(selected_pair)

    return selected_path, control_loc


def generate_binary_file(byte_array):
    byte_list = []
    with open(values.CONF_PATH_POC, "rb") as poc_file:
        byte =poc_file.read(1)
        while byte:
            number = int(struct.unpack('>B', byte)[0])
            byte_list.append(number)
            byte = poc_file.read(1)
    for index in byte_array:
        byte_list[index] = byte_array[index]
    file_extension = str(values.CONF_PATH_POC).split(".")[-1]
    values.FILE_POC_GEN = definitions.DIRECTORY_OUTPUT + "/input-" + str(values.ITERATION_NO) + "." + file_extension

    with open(values.FILE_POC_GEN, "wb") as new_input_file:
        new_input_file.write(bytearray(byte_list))


def generate_new_input(argument_list, second_var_list, patch_list=None):
    """
    This function will select a new path for the next concolic execution and generate the inputs that satisfies the path
           log_path : log file for the previous concolic execution that captures PPC
           project_path: project path is the root directory of the program to filter PPC from libraries
    """
    logger.info("generating new input for new path")
    global list_path_explored, list_path_detected, count_discovered
    gen_arg_list = dict()
    gen_var_list = dict()
    input_var_list = list()
    input_arg_dict = dict()
    input_arg_list = list()
    # input_file_byte_list = list()
    # input_file_stat_byte_list = list()
    if oracle.is_loc_in_trace(values.CONF_LOC_PATCH):
        values.LIST_GENERATED_PATH = generate_symbolic_paths(values.LIST_PPC)
    generated_path_list = values.LIST_GENERATED_PATH
    var_expr_map = reader.collect_symbolic_expression(values.FILE_EXPR_LOG)

    # generated_path_list = generate_new_symbolic_paths(constraint_list)
    # list_path_explored = list(set(list_path_explored + current_path_list))
    selected_patch = None
    patch_constraint = TRUE
    new_path_count = 0

    if oracle.is_loc_in_trace(values.CONF_LOC_PATCH):
        for control_loc, generated_path, ppc_len in generated_path_list:
            if str(generated_path.serialize()) not in (list_path_observed + list_path_explored):
                list_path_detected.append((control_loc, generated_path, ppc_len))
                list_path_observed.append(str(generated_path.serialize()))
                new_path_count = new_path_count + 1

    count_discovered = count_discovered + new_path_count
    emitter.highlight("\tidentified " + str(new_path_count) + " new path(s)")
    emitter.highlight("\ttotal discovered: " + str(count_discovered) + " path(s)")

    if not list_path_detected:
        emitter.debug("Count paths explored: ", str(len(list_path_explored)))
        emitter.debug("Count paths detected: ", str(len(list_path_detected)))
        return None, None, patch_list

    selected_new_path, selected_control_loc = select_new_path_condition()
    list_path_explored.append(str(selected_new_path.serialize()))
    emitter.highlight("\tSelected control location: " + selected_control_loc)
    emitter.highlight("\tSelected path: " + str(selected_new_path))

    # relationship = extractor.extract_var_relationship(var_expr_map)
    # relationship = TRUE
    # selected_new_path = And(selected_new_path, relationship)
    # result_list = parallel.validate_input_generation(patch_list, selected_new_path)
    # filtered_patch_list = list()
    # for result in result_list:
    #     is_valid, index = result
    #     selected_patch = patch_list[index]
    #     if is_valid:
    #         filtered_patch_list.append(selected_patch)
    # #     else:
    # #         # emitter.debug("Removing Patch", selected_patch)
    # #         emitter.emit_patch(selected_patch, message="\t\tRemoving Patch: ")
    # # patch_list = filtered_patch_list
    # if not filtered_patch_list:
    #     emitter.debug("Count paths explored: ", str(len(list_path_explored)))
    #     emitter.debug("Count paths detected: ", str(len(list_path_detected)))
    #     return None, None, {}

    # if values.CONF_SELECTION_STRATEGY == "deterministic":
    #     selected_patch = filtered_patch_list[0]
    # else:
    #     selected_patch = random.choice(filtered_patch_list)

    # emitter.emit_patch(selected_patch, message="\tSelected patch: ")
    # patch_constraint = extractor.extract_constraints_from_patch(selected_patch)
    # add patch constraint and user-input->prog-var relationship
    # selected_new_path = And(selected_new_path, patch_constraint)
    model = z3_get_model(selected_new_path)
    if model is None:
        return None, None, patch_list
    for var_name in model:
        var_byte_list = model[var_name]
        if "arg" in var_name:
            gen_arg_list[var_name] = var_byte_list
        else:
            gen_var_list[var_name] = var_byte_list

    for arg_name in gen_arg_list:
        bit_vector = gen_arg_list[arg_name]
        arg_index = int(str(arg_name).replace("arg", ""))
        arg_str = get_str_value(bit_vector)
        arg_value = get_signed_value(bit_vector) - 48
        # print(arg_name, arg_index, arg_value)
        if str(argument_list[arg_index]).isnumeric():
            input_arg_dict[arg_index] = str(arg_value)
            emitter.debug(arg_name, arg_value)
        else:
            input_arg_dict[arg_index] = arg_str
            emitter.debug(arg_name, arg_str)

    # fill random values if not generated
    offset = 0
    for arg in argument_list:
        index = list(argument_list).index(arg) - offset
        if "$POC" in arg:
            input_arg_list.append(str(argument_list[index]))
            offset = 1
        elif str(index) in values.CONF_MASK_ARG:
            input_arg_list.append(arg)
        elif index in input_arg_dict:
            input_arg_list.append(input_arg_dict[index])
        else:
            arg_len = len(str(argument_list[index]))
            random_value = ""
            for j in range(0, arg_len):
                random_value += chr(random.randint(0, 128))
            input_arg_list.append(random_value)

    for var_name in gen_var_list:
        bit_vector = gen_var_list[var_name]
        var_value = 0
        var_size = len(bit_vector)
        if var_name in ["A-data", "A-data-stat"]:
            if var_name == "A-data":
                generate_binary_file(bit_vector)
            continue
        if bit_vector:
            var_value = get_signed_value(bit_vector)
        emitter.debug(var_name, var_value)
        input_var_list.append({"identifier": var_name, "value": var_value, "size": 4})

    # for var_tuple in second_var_list:
    #     var_name = var_tuple['identifier']
    #     if var_name not in gen_var_list:
    #         emitter.warning("\t[warning] variable " + var_name + " assigned random value")
    #         var_size = var_tuple['size']
    #         var_value = 0
    #         for i in range(1, var_size):
    #             var_value += ((2 << 7) << (int(i) - 1)) * random.randint(0, 255)
    #         input_var_list.append({"identifier": var_name, "value": var_value, "size": var_size})
    emitter.debug("Generated Arg List", input_arg_list)
    emitter.debug("Generated Var List", input_var_list)
    return input_arg_list, input_var_list, patch_list


def generate_ktest(argument_list, second_var_list, print_output=False):
    """
    This function will generate the ktest file provided the argument list and second order variable list
        argument_list : a list containing each argument in the order that should be fed to the program
        second_var_list: a list of tuples where a tuple is (var identifier, var size, var value)
    """
    global File_Ktest_Path

    logger.info("creating ktest file")
    emitter.normal("\tgenerating ktest file")
    ktest_path = File_Ktest_Path
    ktest_command = "gen-bout --out-file {0}".format(ktest_path)
    for argument in argument_list:
        if "$POC" in argument:
            binary_file_path = values.CONF_PATH_POC
            if values.FILE_POC_GEN:
                binary_file_path = values.FILE_POC_GEN
            ktest_command += " --sym-file " + binary_file_path
        else:
            ktest_command += " --sym-arg \"" + str(argument) + "\""

    for var in second_var_list:
        ktest_command += " --second-var \'{0}\' {1} {2}".format(var['identifier'], var['size'], var['value'])
    return_code = execute_command(ktest_command)
    return ktest_path, return_code


def run_concolic_execution(program, argument_list, second_var_list, print_output=False):
    """
    This function will execute the program in concolic mode using the generated ktest file
        program: the absolute path of the bitcode of the program
        argument_list : a list containing each argument in the order that should be fed to the program
        second_var_list: a list of tuples where a tuple is (var identifier, var size, var value)
    """
    logger.info("running concolic execution")

    global File_Log_Path
    current_dir = os.getcwd()
    directory_path = "/".join(str(program).split("/")[:-1])
    emitter.debug("changing directory:", directory_path)
    project_path = values.CONF_PATH_PROJECT
    os.chdir(directory_path)
    binary_name = str(program).split("/")[-1]
    input_argument = ""
    # argument_list = str(argument_str).split(" ")
    for argument in argument_list:
        if "$POC" in argument:
            file_path = values.CONF_PATH_POC
            if values.FILE_POC_GEN:
                file_path = values.FILE_POC_GEN
            concrete_file = open(file_path, 'rb')
            bit_size = os.fstat(concrete_file.fileno()).st_size
            input_argument += " A --sym-files 1 " + str(bit_size) + " "
        else:
            input_argument += " --sym-arg " + str(len(str(argument)))
    ktest_path, return_code = generate_ktest(argument_list, second_var_list)
    ktest_log_file = "/tmp/ktest.log"
    ktest_command = "ktest-tool " + ktest_path + " > " + ktest_log_file
    execute_command(ktest_command)
    bit_length_list = reader.read_bit_length(ktest_log_file)
    if values.LIST_BIT_LENGTH:
        for var in bit_length_list:
            if var in values.LIST_BIT_LENGTH:
                if values.LIST_BIT_LENGTH[var] < bit_length_list[var]:
                    values.LIST_BIT_LENGTH[var] = bit_length_list[var]
            else:
                values.LIST_BIT_LENGTH[var] = bit_length_list[var]
    else:
        values.LIST_BIT_LENGTH = bit_length_list
    emitter.normal("\texecuting klee in concolic mode")
    hit_location_flag = " "
    runtime_lib_path = definitions.DIRECTORY_RUNTIME + "/libtrident_runtime.bca"
    if values.CONF_DISTANCE_METRIC == "control-loc":
        hit_location_flag = "--hit-locations " + values.CONF_LOC_BUG + "," + values.CONF_LOC_PATCH + " "
    klee_command = "klee " \
                   "--posix-runtime " \
                   "--libc=uclibc " \
                   "--write-smt2s " \
                   "-allow-seed-extension " \
                   "-named-seed-matching " \
                   "--log-ppc " \
                   "--resolve-path " \
                   "--log-trace " \
                   + "--external-calls=all " \
                   + "--link-llvm-lib={0} " .format(runtime_lib_path) \
                   + "--max-time={0} ".format(values.DEFAULT_TIMEOUT_KLEE) \
                   + "{0}".format(hit_location_flag) \
                   + "--max-forks {0} ".format(values.DEFAULT_MAX_FORK) \
                   + values.CONF_KLEE_FLAGS + " " \
                   + "--seed-out={0} ".format(ktest_path) \
                   + "{0} ".format(binary_name) \
                   + input_argument
    if not print_output:
        klee_command += " > " + File_Log_Path + " 2>&1 "
    return_code = execute_command(klee_command)
    emitter.debug("changing directory:", current_dir)
    os.chdir(current_dir)

    # collect artifacts
    ppc_log_path = directory_path + "/klee-last/ppc.log"
    trace_log_path = directory_path + "/klee-last/trace.log"
    values.LIST_PPC, last_path = reader.collect_symbolic_path(ppc_log_path, project_path)
    values.PREFIX_PPC_STR = reader.collect_symbolic_path_prefix(ppc_log_path, project_path)
    values.PREFIX_PPC_FORMULA = generate_formula(values.PREFIX_PPC_STR)
    values.LIST_TRACE = reader.collect_trace(trace_log_path, project_path)
    ppc_list = values.LIST_PPC
    return return_code


def run_concrete_execution(program, argument_list, print_output=False, output_dir=None):
    """
    This function will execute the program in concrete mode using the concrete inputs
        program: the absolute path of the bitcode of the program
        argument_list : a list containing each argument in the order that should be fed to the program
        second_var_list: a list of tuples where a tuple is (var identifier, var size, var value)
    """
    logger.info("running concolic execution")
    emitter.normal("\texecuting klee in concrete mode")
    global File_Log_Path
    current_dir = os.getcwd()
    directory_path = "/".join(str(program).split("/")[:-1])
    emitter.debug("changing directory:", directory_path)
    os.chdir(directory_path)
    binary_name = str(program).split("/")[-1]
    input_argument = ""
    runtime_lib_path = definitions.DIRECTORY_RUNTIME + "/libtrident_runtime.bca"
    for argument in argument_list:
        if "$POC" in argument:
            argument = values.CONF_PATH_POC
        input_argument += " " + str(argument)
    if output_dir:
        klee_command = "klee --output-dir=" + str(output_dir) + " "
    else:
        klee_command = "klee "
    klee_command += "--posix-runtime " \
                    "--libc=uclibc " \
                    "--write-smt2s " \
                    "--log-ppc " \
                    "--external-calls=all " \
                    "--max-forks {0} ".format(values.DEFAULT_MAX_FORK) \
                    + values.CONF_KLEE_FLAGS + " " \
                    + "--link-llvm-lib={0} ".format(runtime_lib_path) \
                    + "{0} ".format(binary_name) \
                    + input_argument
    if not print_output:
        klee_command += " > " + File_Log_Path + " 2>&1 "
    return_code = execute_command(klee_command)
    emitter.debug("changing directory:", current_dir)
    os.chdir(current_dir)
    return return_code


def run_concolic_exploration(program, argument_list, second_var_list):
    """
    This function will explore all possible paths in a program provided one single test case
        program: the absolute path of the bitcode of the program
        argument_list : a list containing each argument in the order that should be fed to the program
        second_var_list: a list of tuples where a tuple is (var identifier, var size, var value)
    """
    logger.info("running concolic exploration")
    global list_path_explored, list_path_detected
    run_concolic_execution(program, argument_list, second_var_list, print_output=False)
    is_initial = True
    path_count = 1
    while list_path_detected or is_initial:
        is_initial = False
        path_count = path_count + 1
        gen_arg_list, gen_var_list = generate_new_input(argument_list, second_var_list)
        run_concolic_execution(program, gen_arg_list, gen_var_list)

    print("Explored {0} number of paths".format(path_count))
