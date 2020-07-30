import logging
import subprocess
from typing import List, Dict, Tuple, Set, Union, Optional, NamedTuple
import os
import collections
import random
from six.moves import cStringIO
from pysmt.shortcuts import get_model, Solver, And, Not, is_sat
from pysmt.smtlib.parser import SmtLibParser
from pysmt.shortcuts import is_sat, get_model, Symbol, BV, Equals, EqualsOrIff, And, Or, TRUE, FALSE, Select, BVConcat
import pysmt.environment

logger = logging.getLogger(__name__)

Formula = Union[pysmt.fnode.FNode]
File_Klee_Path = "/tmp/log_sym_path"
File_Ktest_Path = "/tmp/concolic.ktest"

list_path_explored = list()
list_path_detected = list()


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
    constraint_list = dict()
    for control_loc in reversed(ppc_list):
        ppc = ppc_list[control_loc]
        ppc = "".join(ppc)
        parser = SmtLibParser()
        script = parser.get_script(cStringIO(ppc))
        formula = script.get_last_formula()
        constraint = formula.arg(1)
        print(control_loc, constraint)
        if control_loc not in constraint_list:
            constraint_list[control_loc] = list()
        constraint_list[control_loc].append(constraint)
    return constraint_list


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
                        continue
                    new_path = And(new_path, constraint)
            if is_sat(new_path):
                if new_path not in new_path_list:
                    new_path_list.append(new_path)

    return new_path_list


def generate_new_input(log_path, project_path):
    """
    This function will select a new path for the next concolic execution and generate the inputs that satisfies the path
           log_path : log file for the previous concolic execution that captures PPC
           project_path: project path is the root directory of the program to filter PPC from libraries
    """
    logger.info("creating new path for concolic execution")
    global list_path_explored, list_path_detected
    argument_list = list()
    second_var_list = list()
    ppc_list, last_path = collect_symbolic_path(log_path, project_path)
    constraint_list = analyse_symbolic_path(ppc_list)
    new_path_list = generate_new_symbolic_paths(constraint_list)
    for new_path in new_path_list:
        if new_path not in (list_path_detected + list_path_explored):
            list_path_detected.append(new_path)
    selected_new_path = random.choice(list_path_detected)
    list_path_explored.append(selected_new_path)
    list_path_detected.remove(selected_new_path)
    model = get_model(selected_new_path)
    print(model)


def generate_ktest(argument_list, second_var_list):
    """
    This function will generate the ktest file provided the argument list and second order variable list
        argument_list : a list containing each argument in the order that should be fed to the program
        second_var_list: a list of tuples where a tuple is (var identifier, var size, var value)
    """
    global File_Ktest_Path
    logger.info("creating ktest file")
    ktest_path = File_Ktest_Path
    ktest_command = "gen-bout --out-file={0}".format(ktest_path)
    n_arg = str(len(argument_list))
    ktest_command += " --sym-args " + n_arg
    for argument in argument_list:
        ktest_command += " " + str(argument)

    for var in second_var_list:
        ktest_command += " --second-var {0} {1} {2}".format(var['identifier'], var['size'], var['value'])
    process = subprocess.Popen([ktest_command], stdout=subprocess.PIPE, shell=True)
    (output, error) = process.communicate()
    return ktest_path, process.returncode


def run_concolic_execution(program, argument_list, second_var_list):
    """
    This function will execute the program in concolic mode using the generated ktest file
        argument_list : a list containing each argument in the order that should be fed to the program
        second_var_list: a list of tuples where a tuple is (var identifier, var size, var value)
    """
    logger.info("running concolic execution")
    input_argument = ""
    for argument in argument_list:
        input_argument += " --sym-arg " + str(len(argument))
    ktest_path = generate_ktest(argument_list, second_var_list)
    klee_command = "klee " \
                   "--posix-runtime " \
                   "--libc=uclibc " \
                   "--write-smt2s " \
                   "--external-calls=all " \
                   + "--seed-out={0} ".format(ktest_path) \
                   + "{0}.bc ".format(program) \
                   + input_argument

    process = subprocess.Popen([klee_command], stdout=subprocess.PIPE, shell=True)
    (output, error) = process.communicate()
    return process.returncode
