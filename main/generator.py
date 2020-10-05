from main.synthesis import load_specification, synthesize, Program
from pathlib import Path
from typing import List, Dict, Tuple
from six.moves import cStringIO
from pysmt.shortcuts import is_sat, Not, And, TRUE
import os
from pysmt.smtlib.parser import SmtLibParser
from pysmt.typing import BV32, BV8, ArrayType
from pysmt.shortcuts import write_smtlib, get_model, Symbol
from main.utilities import execute_command
from main import emitter, values, reader, parallel, definitions, extractor, oracle, utilities, logger
import re
import struct
import random

File_Log_Path = "/tmp/log_sym_path"
File_Ktest_Path = "/tmp/concolic.ktest"

def generate_patch_set(project_path) -> List[Dict[str, Program]]:

    definitions.FILE_PATCH_SET = definitions.DIRECTORY_OUTPUT + "/patch-set"

    if values.CONF_SKIP_GEN:
        emitter.sub_title("Loading Patch Pool")
        list_of_patches = reader.read_pickle(definitions.FILE_PATCH_SET)
        emitter.normal("\tnumber of patches in pool: " + str(len(list_of_patches)))
        return list_of_patches

    emitter.sub_title("Generating Patch Pool")
    test_output_list = values.CONF_TEST_OUTPUT
    components = values.LIST_COMPONENTS
    depth = values.DEFAULT_DEPTH
    if values.CONF_DEPTH_VALUE.isnumeric():
        depth = int(values.CONF_DEPTH_VALUE)

    spec_files = []
    binary_dir_path = "/".join(values.CONF_PATH_PROGRAM.split("/")[:-1])
    for output_spec in test_output_list:
        output_spec_path = Path(project_path + "/" + output_spec)
        test_index = str((int(test_output_list.index(output_spec)) * 2) )
        klee_spec_path = Path(binary_dir_path + "/klee-out-" + test_index)
        spec_files.append((output_spec_path, klee_spec_path))
    specification = load_specification(spec_files)
    values.TEST_SPECIFICATION = specification
    concrete_enumeration = False
    if values.CONF_PATCH_TYPE == values.OPTIONS_PATCH_TYPE[0]:
        concrete_enumeration = True
    lower_bound = values.DEFAULT_LOWER_BOUND
    upper_bound = values.DEFAULT_UPPER_BOUND

    result = synthesize(components, depth, specification, concrete_enumeration, lower_bound, upper_bound)

    list_of_patches = [_ for _ in result]
    # writer.write_as_pickle(list_of_patches, definitions.FILE_PATCH_SET)
    emitter.normal("\tnumber of patches in pool: " + str(len(list_of_patches)))
    return list_of_patches


def generate_flipped_path(ppc):
    """
    This function will check if a selected path is feasible
           ppc : partial path conditoin at chosen control loc
           chosen_control_loc: branch location selected for flip
           returns satisfiability of the negated path
    """
    parser = SmtLibParser()
    script = parser.get_script(cStringIO(ppc))
    formula = script.get_last_formula()
    prefix = formula.arg(0)
    constraint = formula.arg(1)
    new_path = And(prefix, Not(constraint))

    assert str(new_path.serialize()) != str(formula.serialize())
    return new_path


def generate_angelic_val_for_crash(klee_out_dir):
    file_list = [os.path.join(klee_out_dir, f) for f in os.listdir(klee_out_dir) if os.path.isfile(os.path.join(klee_out_dir,f))]
    error_file_path = None
    for file_name in file_list:
        if ".err" in file_name:
            error_file_path = file_name.split(".")[0] + ".smt2"
            break
    sym_path = extractor.extract_assertion(error_file_path)
    input_arg_list, input_var_list = generate_new_input(sym_path, values.ARGUMENT_LIST)
    return input_arg_list, input_var_list


def generate_mask_bytes(klee_out_dir):
    mask_byte_list = list()
    log_path = klee_out_dir + "/concrete.log"
    concretized_byte_list = reader.collect_concretized_bytes(log_path)
    smt2_file_path = klee_out_dir + "/test000001.smt2"
    control_byte_list = reader.collect_bytes_from_smt2(smt2_file_path)
    emitter.debug("Control Byte List", control_byte_list)
    fixed_byte_list = list()
    if "A-data" in concretized_byte_list:
        influence_byte_list = sorted(list(concretized_byte_list["A-data"]))
        emitter.debug("Influencing Byte List", influence_byte_list)
    fixed_byte_list = control_byte_list
    if values.CONF_PATH_POC:
        byte_length = os.path.getsize(values.CONF_PATH_POC)
        for i in range(0, byte_length):
            if i not in fixed_byte_list:
                mask_byte_list.append(i)
    return sorted(mask_byte_list)


def generate_model(formula):
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


def generate_new_input(sym_path, argument_list):
    gen_arg_list = dict()
    gen_var_list = dict()
    input_var_list = list()
    input_arg_dict = dict()
    input_arg_list = list()
    model = generate_model(sym_path)
    if model is None:
        return None, None
    for var_name in model:
        var_byte_list = model[var_name]
        if "arg" in var_name:
            gen_arg_list[var_name] = var_byte_list
        else:
            gen_var_list[var_name] = var_byte_list

    for arg_name in gen_arg_list:
        bit_vector = gen_arg_list[arg_name]
        arg_index = int(str(arg_name).replace("arg", ""))
        arg_str = utilities.get_str_value(bit_vector)
        arg_value = utilities.get_signed_value(bit_vector) - 48
        # print(arg_name, arg_index, arg_value)
        if str(argument_list[arg_index]).isnumeric():
            input_arg_dict[arg_index] = str(arg_value)
            # emitter.debug(arg_name, arg_value)
        else:
            input_arg_dict[arg_index] = arg_str
            # emitter.debug(arg_name, arg_str)

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
            var_value = utilities.get_signed_value(bit_vector)
        # emitter.debug(var_name, var_value)
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
    return input_arg_list, input_var_list


def generate_model_cli(formula):
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


def generate_binary_file(byte_array):
    byte_list = []
    modified_index_list = []
    with open(values.CONF_PATH_POC, "rb") as poc_file:
        byte =poc_file.read(1)
        while byte:
            number = int(struct.unpack('>B', byte)[0])
            byte_list.append(number)
            byte = poc_file.read(1)
    emitter.debug("Masked Byte List", values.MASK_BYTE_LIST)
    for index in byte_array:
        if index not in values.MASK_BYTE_LIST:
            byte_list[index] = byte_array[index]
            modified_index_list.append(index)
    emitter.debug("Modified Byte List", modified_index_list)
    file_extension = str(values.CONF_PATH_POC).split(".")[-1]
    values.FILE_POC_GEN = definitions.DIRECTORY_OUTPUT + "/input-" + str(values.ITERATION_NO) + "." + file_extension

    with open(values.FILE_POC_GEN, "wb") as new_input_file:
        new_input_file.write(bytearray(byte_list))


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
        path_count = path_count + 1
        path_list.append(result)

    emitter.highlight("\t\tgenerated " + str(path_count) + " flipped path(s)")
    return path_list


def generate_ktest(argument_list, second_var_list, print_output=False):
    """
    This function will generate the ktest file provided the argument list and second order variable list
        argument_list : a list containing each argument in the order that should be fed to the program
        second_var_list: a list of tuples where a tuple is (var identifier, var size, var value)
    """
    global File_Ktest_Path

    logger.log("creating ktest file")
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


def generate_path_for_negation():
    constraint_list = []
    parser = SmtLibParser()
    emitter.normal("\tgenerating path for negation of patch constraint")
    for control_loc, sym_path in values.LIST_PPC:
        if control_loc == values.CONF_LOC_PATCH:
            script = parser.get_script(cStringIO(sym_path))
            formula = script.get_last_formula()
            patch_constraint = formula.arg(1)
            constraint_list.append(patch_constraint.serialize())

    last_sym_path = values.LAST_PPC_FORMULA
    script = parser.get_script(cStringIO(last_sym_path))
    formula = script.get_last_formula()
    negated_path = None
    while constraint_list:
        constraint = formula.arg(1)
        constraint_str = constraint.serialize()
        if constraint_str in constraint_list:
            constraint_list.remove(constraint_str)
            constraint = Not(constraint)
        if negated_path is None:
            negated_path = constraint
        else:
            negated_path = And(negated_path, constraint)
        formula = formula.arg(0)
    return negated_path
