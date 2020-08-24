import logging
from typing import List, Dict, Tuple, Set, Union, Optional, NamedTuple
import os
import re
import collections
import random
from six.moves import cStringIO
from pysmt.shortcuts import get_model, Solver, And, Not, is_sat
from pysmt.shortcuts import is_sat, get_model, Symbol, BV, Equals, EqualsOrIff, And, Or, TRUE, FALSE, Select, BVConcat, Int
import pysmt.environment
from pysmt.smtlib.parser import SmtLibParser
from pysmt.typing import BOOL, BV32, BV8, ArrayType
from pysmt.shortcuts import write_smtlib, get_model, Symbol
from main.utilities import execute_command, extract_constraints_from_patch
from main import emitter


logger = logging.getLogger(__name__)
Formula = Union[pysmt.fnode.FNode]
File_Log_Path = "/tmp/log_sym_path"
File_Ktest_Path = "/tmp/concolic.ktest"

list_path_explored = list()
list_path_detected = list()


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
            array_size = 4 #TODO: dynamically calculate the size later
            for i in range(0, array_size):
                byte_list[i] = default_value
            for idx, val in value_array_map.items():
                index = int(str(idx).split("_")[0])
                value = int(str(val).split("_")[0])
                byte_list[index] = value
            for i in range(3, -1, -1):
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
    collect_lambda = False
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
                    str_value = str_lambda.replace("(lambda ((x!1 (_ BitVec 32))) ", "").replace("))", "").replace("\n", "")
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


def collect_symbolic_expression(log_path):
    """
       This function will read the output log of a klee concolic execution and extract symbolic expressions
       of variables of interest
    """
    var_expr_map = list()
    if os.path.exists(log_path):
        with open(log_path, 'r') as trace_file:
            expr_pair = None
            for line in trace_file:
                if '[klee:expr]' in line:
                    line = line.split("[klee:expr] ")[-1]
                    var_name, var_expr = line.split(": ")
                    var_expr = var_expr.replace("\n", "")
                    if "[program-var]" in var_name:
                        expr_pair = var_expr
                    elif "[angelic-var]" in var_name:
                        expr_pair = (expr_pair, var_expr)
                        if expr_pair not in var_expr_map:
                            var_expr_map.append(expr_pair)
    return var_expr_map


def collect_symbolic_path(log_path, project_path):
    """
       This function will read the output log of a klee concolic execution and extract the partial path conditions
    """
    ppc_list = collections.OrderedDict()
    last_sym_path = ""
    if os.path.exists(log_path):
        source_path = ""
        path_condition = ""
        with open(log_path, 'r') as trace_file:
            for line in trace_file:
                if '[path:ppc]' in line:
                    if project_path in line:
                        source_path = str(line.replace("[path:ppc]", '')).split(" : ")[0]
                        source_path = source_path.strip()
                        source_path = os.path.abspath(source_path)
                        path_condition = str(line.replace("[path:ppc]", '')).split(" : ")[1]
                        continue
                if source_path:
                    if "(exit)" not in line:
                        path_condition = path_condition + line
                    else:
                        if source_path not in ppc_list.keys():
                            ppc_list[source_path] = list()
                        ppc_list[source_path].append((path_condition))
                        last_sym_path = path_condition
                        source_path = ""
                        path_condition = ""
    # constraints['last-sym-path'] = last_sym_path
    # print(constraints.keys())
    return ppc_list, last_sym_path


def analyse_symbolic_path(ppc_list):
    """
       This function will analyse the partial path conditions collected at each branch location and isolate
       the branch conditions added at each location, which can be used to negate as a constraint
              ppc_list : a dictionary containing the partial path condition at each branch location
    """
    constraint_list = collections.OrderedDict()
    explored_path_list = list()
    current_path = None
    for control_loc in ppc_list:
        ppc = ppc_list[control_loc]
        ppc = "".join(ppc)
        parser = SmtLibParser()
        script = parser.get_script(cStringIO(ppc))
        formula = script.get_last_formula()
        constraint = formula.arg(1)
        # print(control_loc, constraint)
        if control_loc not in constraint_list:
            constraint_list[control_loc] = list()
        constraint_list[control_loc].append(constraint)
        if current_path is None:
            current_path = constraint
        else:
            current_path = And(current_path, constraint)
        explored_path_list.append(current_path)
    return constraint_list, explored_path_list


def generate_new_symbolic_paths(constraint_list):
    """
    This function will generate N number of new paths by negating each branch condition at a given branch location
           constraint_list : a dictionary containing the constraints at each branch location
    """
    new_path_list = list()
    for chosen_control_loc in constraint_list:
        chosen_constraint_list_at_loc = constraint_list[chosen_control_loc]
        for chosen_constraint in chosen_constraint_list_at_loc:
            new_path = Not(chosen_constraint)
            for control_loc in constraint_list:
                constraint_list_at_loc = constraint_list[control_loc]
                for constraint in constraint_list_at_loc:
                    if constraint == chosen_constraint and control_loc == chosen_control_loc:
                        if is_sat(new_path):
                            if new_path not in new_path_list:
                                new_path_list.append(new_path)
                        break
                    new_path = And(new_path, constraint)
                if control_loc == chosen_control_loc:
                    break

    return new_path_list


def get_signed_value(bit_vector):
    """
      This function will generate the signed value for a given byte list
             bit_vector : list of bytes
    """
    signed_value = 0
    for i in bit_vector:
        if i == 0:
            signed_value = int(bit_vector[i])
        else:
            signed_value += ((2 << 7) << (int(i) - 1)) * int(bit_vector[i])
    return signed_value


def get_str_value(bit_vector):
    """
      This function will generate the string value for a given byte list
             bit_vector : list of bytes
    """
    str_value = ""
    char_list = dict()
    # print(bit_vector)
    for i in bit_vector:
        if int(bit_vector[i]) not in range(48, 127):
            char_list[i] = chr(random.randint(49, 122))
        else:
            char_list[i] = chr(bit_vector[i])
    # print(char_list)
    for i in sorted(char_list, reverse=True):
        char = char_list[i]
        str_value += char
    return str_value


def generate_new_input(ppc_log_path, expr_log_path, project_path, argument_list, second_var_list, patch_list=None):
    """
    This function will select a new path for the next concolic execution and generate the inputs that satisfies the path
           log_path : log file for the previous concolic execution that captures PPC
           project_path: project path is the root directory of the program to filter PPC from libraries
    """
    logger.info("creating new path for concolic execution")
    global list_path_explored, list_path_detected
    gen_arg_list = dict()
    gen_var_list = dict()
    input_var_list = list()
    input_arg_dict = dict()
    input_arg_list = list()
    ppc_list, last_path = collect_symbolic_path(ppc_log_path, project_path)
    var_expr_map = collect_symbolic_expression(expr_log_path)
    constraint_list, current_path_list = analyse_symbolic_path(ppc_list)
    new_path_list = generate_new_symbolic_paths(constraint_list)
    # list_path_explored = list(set(list_path_explored + current_path_list))
    selected_patch = None
    patch_constraint = TRUE

    for new_path in new_path_list:
        if new_path not in (list_path_detected + list_path_explored):
            list_path_detected.append(new_path)

    if not list_path_detected:
        emitter.debug("Count paths explored: ", str(len(list_path_explored)))
        emitter.debug("Count paths detected: ", str(len(list_path_detected)))
        return None, None, patch_list
    selected_new_path = random.choice(list_path_detected)
    list_path_explored.append(selected_new_path)
    list_path_detected.remove(selected_new_path)

    # preserve user-input : program variable relationship
    parser = SmtLibParser()
    relationship = None
    for expr_map in var_expr_map:
        prog_var_expr = expr_map[0]
        angelic_var_expr = expr_map[1]
        prog_dependent_var_list = set(re.findall("\(select (.+?) \(_ ", prog_var_expr))
        angelic_dependent_var_list = set(re.findall("\(select (.+?) \(_ ", angelic_var_expr))
        dependent_var_list = set(list(prog_dependent_var_list) + list(angelic_dependent_var_list))
        str_script = "(set-logic QF_AUFBV )\n"
        for var_d in dependent_var_list:
            str_script += "(declare-fun " + var_d + " () (Array (_ BitVec 32) (_ BitVec 8) ) )\n"
        str_script += "(assert (= " + prog_var_expr + " " + angelic_var_expr + " ))\n"
        str_script += "(exit)\n"
        script = parser.get_script(cStringIO(str_script))
        formula = script.get_last_formula()
        relationship = formula

    selected_new_path = And(selected_new_path, relationship)

    while patch_list:
        selected_patch = random.choice(patch_list)
        patch_constraint = extract_constraints_from_patch(selected_patch)
        check_sat = And(selected_new_path, patch_constraint)
        if is_sat(check_sat):
            break
        else:
            emitter.debug("Removing Patch", selected_patch)
            patch_list.remove(selected_patch)
    emitter.emit_patch(selected_patch, message="\tSelected patch: ")


    # add patch constraint and user-input->prog-var relationship
    selected_new_path = And(selected_new_path, patch_constraint)
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
        emitter.debug(arg_name, arg_value)
        if str(argument_list[arg_index]).isnumeric():
            input_arg_dict[arg_index] = str(arg_value)
        else:
            input_arg_dict[arg_index] = arg_str

    # fill random values if not generated
    for i in range(0, len(argument_list)):
        if i in input_arg_dict:
            input_arg_list.append(input_arg_dict[i])
        else:
            arg_len = len(str(argument_list[i]))
            random_value = ""
            for j in range(0, arg_len):
                random_value += chr(random.randint(0, 128))
            input_arg_list.append(random_value)

    for var_name in gen_var_list:
        bit_vector = gen_var_list[var_name]
        var_value = 0
        var_size = len(bit_vector)
        if bit_vector:
            var_value = get_signed_value(bit_vector)
        emitter.debug(var_name, var_value)
        input_var_list.append({"identifier": var_name, "value": var_value, "size": 4})

    for var_tuple in second_var_list:
        var_name = var_tuple['identifier']
        if var_name not in gen_var_list:
            emitter.warning("\t[warning] variable " + var_name + " assigned random value")
            var_size = var_tuple['size']
            var_value = 0
            for i in range(1, var_size):
                var_value += ((2 << 7) << (int(i) - 1)) * random.randint(0, 255)
            input_var_list.append({"identifier": var_name, "value": var_value, "size": var_size})
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
    n_arg = str(len(argument_list))
    ktest_command += " --sym-args " + n_arg
    for argument in argument_list:
        ktest_command += " \"" + str(argument) + "\""

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
    os.chdir(directory_path)
    binary_name = str(program).split("/")[-1]
    input_argument = ""
    for argument in argument_list:
        input_argument += " --sym-arg " + str(len(str(argument)))
    ktest_path, return_code = generate_ktest(argument_list, second_var_list)
    emitter.normal("\texecuting klee concolic execution")
    klee_command = "klee " \
                   "--posix-runtime " \
                   "--libc=uclibc " \
                   "--write-smt2s " \
                   "-allow-seed-extension " \
                   "--log-ppc " \
                   "--external-calls=all " \
                   + "--seed-out={0} ".format(ktest_path) \
                   + "{0} ".format(binary_name) \
                   + input_argument
    if not print_output:
        klee_command += " > " + File_Log_Path + " 2>&1 "
    return_code = execute_command(klee_command)
    emitter.debug("changing directory:", current_dir)
    os.chdir(current_dir)
    return return_code


def run_concrete_execution(program, argument_list, second_var_list, print_output=False, output_dir=None):
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
    for argument in argument_list:
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
                   + "{0} ".format(binary_name) \
                   + input_argument
    if not print_output:
        klee_command += " > " + File_Log_Path + " 2>&1 "
    return_code = execute_command(klee_command)
    emitter.debug("changing directory:", current_dir)
    os.chdir(current_dir)
    return return_code


def run_concolic_exploration(program, argument_list, second_var_list, root_directory):
    """
    This function will explore all possible paths in a program provided one single test case
        program: the absolute path of the bitcode of the program
        argument_list : a list containing each argument in the order that should be fed to the program
        second_var_list: a list of tuples where a tuple is (var identifier, var size, var value)
    """
    logger.info("running concolic exploration")
    global list_path_explored, list_path_detected
    run_concolic_execution(program, argument_list, second_var_list, print_output=False)
    ppc_log_path = root_directory + "/klee-last/ppc.log"
    expr_log_path = root_directory + "/klee-last/expr.log"
    is_initial = True
    path_count = 1
    while list_path_detected or is_initial:
        is_initial = False
        path_count = path_count + 1
        gen_arg_list, gen_var_list = generate_new_input(ppc_log_path, expr_log_path, root_directory, argument_list, second_var_list)
        run_concolic_execution(program, gen_arg_list, gen_var_list)

    print("Explored {0} number of paths".format(path_count))
