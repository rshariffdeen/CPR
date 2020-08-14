import logging
import subprocess
from typing import List, Dict, Tuple, Set, Union, Optional, NamedTuple
import os
import re
import collections
import random
from six.moves import cStringIO
from pysmt.shortcuts import get_model, Solver, And, Not, is_sat
from pysmt.smtlib.parser import SmtLibParser
from pysmt.shortcuts import is_sat, get_model, Symbol, BV, Equals, EqualsOrIff, And, Or, TRUE, FALSE, Select, BVConcat
import pysmt.environment
from utilities import z3_get_model

logger = logging.getLogger(__name__)

Formula = Union[pysmt.fnode.FNode]
File_Log_Path = "/tmp/log_sym_path"
File_Ktest_Path = "/tmp/concolic.ktest"

list_path_explored = list()
list_path_detected = list()


def collect_symbolic_expression(log_path):
    """
       This function will read the output log of a klee concolic execution and extract symbolic expressions
       of variables of interest
    """
    var_expr_map = dict()
    if os.path.exists(log_path):
        with open(log_path, 'r') as trace_file:
            for line in trace_file:
                if '[klee:expr]' in line:
                    line = line.split("[klee:expr] ")[-1]
                    var_name, var_expr = line.split(":")
                    var_expr = var_expr.replace("\n", "")
                    if var_name not in var_expr_map.keys():
                        var_expr_map[var_name] = dict()
                        var_expr_map[var_name]['expr_list'] = list()
                    var_expr_map[var_name]['expr_list'].append(var_expr)
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
    signed_value = 0
    for i in bit_vector:
        if i == 0:
            signed_value = int(bit_vector[i])
        else:
            signed_value += ((2 << 7) << (int(i) - 1)) * int(bit_vector[i])
    return signed_value


def get_str_value(bit_vector):
    str_value = ""
    char_list = dict()
    for i in bit_vector:
        if int(bit_vector[i]) > 127:
            char_list[i] = chr(48)
        else:
            char_list[i] = chr(bit_vector[i])

    for i in sorted(char_list, reverse=True):
        char = char_list[i]
        str_value += char
    return str_value


def extract_bit_vector(expression_str):
    bit_vector = dict()
    if "[" in expression_str:
        token_list = expression_str.split("[")
        token_list.remove(token_list[0])
        for token in token_list:
            if ".." in token:
                continue
            index_str, value_str = token.split(" := ")
            index = int(index_str.split("_")[0])
            value = int(value_str.split("_")[0])
            bit_vector[index] = value
    return bit_vector


def generate_new_input(ppc_log_path, expr_log_path, project_path, argument_list, second_var_list, patch_constraint=None):
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
    list_path_explored = list(set(list_path_explored + current_path_list))
    if not patch_constraint:
        patch_constraint = TRUE
    for new_path in new_path_list:
        if new_path not in (list_path_detected + list_path_explored):
            list_path_detected.append(new_path)
    selected_new_path = random.choice(list_path_detected)
    list_path_explored.append(selected_new_path)
    list_path_detected.remove(selected_new_path)

    # preserve user-input : program variable relationship
    parser = SmtLibParser()
    relationship = None
    for var_name in var_expr_map:
        expr_list = var_expr_map[var_name]['expr_list']
        assert len(expr_list) == 2
        for expression in expr_list:
            dependent_var_list = set(re.search("\(select (.+?) \(_", expression))
            str_script = "(set-logic QF_AUFBV )\n"\
                         "(declare-fun " + var_name + " () (Array (_ BitVec 32) (_ BitVec 8) ) )\n"
            for var_d in dependent_var_list:
                str_script += "(declare-fun " + var_d + " () (Array (_ BitVec 32) (_ BitVec 8) ) )\n"
            str_script += "(assert (= " + var_name + " " + expression + " ))\n"
            str_script += "(exit)\n"
            script = parser.get_script(cStringIO(str_script))
            formula = script.get_last_formula()
            if not relationship:
                relationship = formula
            else:
                relationship = Equals(relationship, formula)

    # add patch constraint and user-input->prog-var relationship
    selected_new_path = And(selected_new_path, And(patch_constraint, relationship))
    model = z3_get_model(selected_new_path)

    for var_name in model:
        var_byte_list = model[var_name]
        if "arg" in var_name:
            gen_arg_list[var_name] = var_byte_list
        else:
            gen_var_list[var_name] = var_byte_list

    for arg_name in gen_arg_list:
        bit_vector = gen_arg_list[arg_name]
        arg_index = int(str(arg_name).replace("arg", ""))
        arg_value = get_str_value(bit_vector)
        print(arg_name, arg_value)
        input_arg_dict[arg_index] = arg_value

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
        print(var_name, var_size, var_value)
        input_var_list.append({"identifier": var_name, "value": var_value, "size": var_size})


    for var_tuple in second_var_list:
        var_name = var_tuple['identifier']
        if "angelic" in var_name:
            continue
        if var_name not in gen_var_list:
            print("[warning] variable " + var_name + " assigned random value")
            var_size = var_tuple['size']
            var_value = 0
            for i in range(1, var_size):
                var_value += ((2 << 7) << (int(i) - 1)) * random.randint(0, 255)
            input_var_list.append({"identifier": var_name, "value": var_value, "size": var_size})

    return input_arg_list, input_var_list


def generate_ktest(argument_list, second_var_list, print_output=False):
    """
    This function will generate the ktest file provided the argument list and second order variable list
        argument_list : a list containing each argument in the order that should be fed to the program
        second_var_list: a list of tuples where a tuple is (var identifier, var size, var value)
    """
    global File_Ktest_Path
    logger.info("creating ktest file")
    ktest_path = File_Ktest_Path
    ktest_command = "gen-bout --out-file {0}".format(ktest_path)
    n_arg = str(len(argument_list))
    ktest_command += " --sym-args " + n_arg
    for argument in argument_list:
        ktest_command += " \"" + str(argument) + "\""

    for var in second_var_list:
        ktest_command += " --second-var \"{0}\" {1} {2}".format(var['identifier'], var['size'], var['value'])
    process = subprocess.Popen([ktest_command], stderr=subprocess.PIPE, shell=True)
    (output, error) = process.communicate()
    return ktest_path, process.returncode


def run_concolic_execution(program, argument_list, second_var_list, print_output=False):
    """
    This function will execute the program in concolic mode using the generated ktest file
        program: the absolute path of the bitcode of the program
        argument_list : a list containing each argument in the order that should be fed to the program
        second_var_list: a list of tuples where a tuple is (var identifier, var size, var value)
    """
    logger.info("running concolic execution")
    global File_Log_Path
    input_argument = ""
    for argument in argument_list:
        input_argument += " --sym-arg " + str(len(str(argument)))
    ktest_path, return_code = generate_ktest(argument_list, second_var_list)
    klee_command = "klee " \
                   "--posix-runtime " \
                   "--libc=uclibc " \
                   "--write-smt2s " \
                   "-allow-seed-extension " \
                   "--log-ppc " \
                   "--external-calls=all " \
                   + "--seed-out={0} ".format(ktest_path) \
                   + "{0} ".format(program) \
                   + input_argument
    if not print_output:
        klee_command += " > " + File_Log_Path + " 2>&1 "
    process = subprocess.Popen([klee_command], stderr=subprocess.PIPE, shell=True)
    (output, error) = process.communicate()
    return process.returncode


def run_concrete_execution(program, argument_list, second_var_list, print_output=False):
    """
    This function will execute the program in concrete mode using the concrete inputs
        program: the absolute path of the bitcode of the program
        argument_list : a list containing each argument in the order that should be fed to the program
        second_var_list: a list of tuples where a tuple is (var identifier, var size, var value)
    """
    logger.info("running concolic execution")
    global File_Log_Path
    input_argument = ""
    for argument in argument_list:
        input_argument += " " + str(argument)
    ktest_path, return_code = generate_ktest(argument_list, second_var_list)
    klee_command = "klee " \
                   "--posix-runtime " \
                   "--libc=uclibc " \
                   "--write-smt2s " \
                   "--log-ppc " \
                   "--external-calls=all " \
                   + "{0} ".format(program) \
                   + input_argument
    if not print_output:
        klee_command += " > " + File_Log_Path + " 2>&1 "
    process = subprocess.Popen([klee_command], stderr=subprocess.PIPE, shell=True)
    (output, error) = process.communicate()
    return process.returncode


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
