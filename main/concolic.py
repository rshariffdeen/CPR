import logging
from typing import Union
import os

import random
import operator
from pysmt.shortcuts import is_sat, Not, And, TRUE
import pysmt.environment

import main.generator
from main import emitter, values, reader, utilities, definitions, generator, oracle, parallel, extractor
import numpy


logger = logging.getLogger(__name__)
Formula = Union[pysmt.fnode.FNode]
File_Log_Path = "/tmp/log_sym_path"


list_path_explored = list()
list_path_detected = list()
list_path_infeasible = list()
list_path_inprogress = list()
count_discovered = 0


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


def select_nearest_control_loc():
    selection = None
    control_loc_list = numpy.array(list_path_inprogress)[:, 0]
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
    global list_path_inprogress
    if values.CONF_DISTANCE_METRIC == values.OPTIONS_DIST_METRIC[0]:
        path_list_at_patch_loc = [(p[1], p[2], p[3], p[4]) for p in list_path_inprogress if p[0] == values.CONF_LOC_PATCH]
        if path_list_at_patch_loc:
            control_loc = values.CONF_LOC_PATCH
            selected_pair = (max(path_list_at_patch_loc, key=lambda item: item[1]))
            selected_path = selected_pair[0]
            selected_pair = (values.CONF_LOC_PATCH, selected_pair[0], selected_pair[1], selected_pair[2], selected_pair[3])
        else:
            selected_pair = max(list_path_inprogress, key=lambda item: item[2])
            selected_path = selected_pair[1]
            control_loc = selected_pair[0]
        list_path_inprogress.remove(selected_pair)
    elif values.CONF_DISTANCE_METRIC == values.OPTIONS_DIST_METRIC[1]:
        control_loc = select_nearest_control_loc()
        path_list_at_loc = [(p[1], p[2], p[3], p[4]) for p in list_path_inprogress if p[0] == control_loc]
        if values.CONF_SELECTION_STRATEGY == "deterministic":
            selected_pair = (max(path_list_at_loc, key=lambda item: item[1]))
            selected_path = selected_pair[0]
            selected_pair = (control_loc, selected_pair[0], selected_pair[1], selected_pair[2], selected_pair[3])
        else:
            selected_pair = (random.choice(path_list_at_loc))
            selected_path = selected_pair[1]
            control_loc = selected_pair[0]
            selected_pair = (control_loc, selected_pair[0], selected_pair[1], selected_pair[2], selected_pair[3])
        list_path_inprogress.remove(selected_pair)
    else:
        ranked_list = sorted(list_path_inprogress, key=operator.itemgetter(4, 3, 2))
        if values.CONF_SELECTION_STRATEGY == "deterministic":
            selected_pair = ranked_list[0]
            selected_path = selected_pair[1]
            control_loc = selected_pair[0]
        else:
            selected_pair = (random.choice(ranked_list))
            selected_path = selected_pair[1]
            control_loc = selected_pair[0]
        list_path_inprogress.remove(selected_pair)

    return selected_path, control_loc


def select_patch_constraint_for_input(patch_list, selected_new_path):
    # relationship = extractor.extract_var_relationship(var_expr_map)
    # relationship = TRUE
    # selected_new_path = And(selected_new_path, relationship)
    result_list = parallel.validate_input_generation(patch_list, selected_new_path)
    filtered_patch_list = list()
    for result in result_list:
        is_valid, index = result
        selected_patch = patch_list[index]
        if is_valid:
            filtered_patch_list.append(selected_patch)

    if not filtered_patch_list:
        # emitter.note("\t\tCount paths explored: " + str(len(list_path_explored)))
        # emitter.note("\t\tCount paths remaining: " + str(len(list_path_detected)))
        return None

    if values.CONF_SELECTION_STRATEGY == "deterministic":
        selected_patch = filtered_patch_list[0]
    else:
        selected_patch = random.choice(filtered_patch_list)

    emitter.emit_patch(selected_patch, message="\t\tSelected patch: ")
    patch_formula = main.generator.generate_formula_from_patch(selected_patch)
    patch_formula_extended = generator.generate_extended_patch_formula(patch_formula, selected_new_path)
    patch_space_constraint = patch_formula_extended
    if values.CONF_PATCH_TYPE == values.OPTIONS_PATCH_TYPE[1]:
        patch_formula_str = str(patch_formula.serialize())
        patch_index = utilities.get_hash(patch_formula_str)
        patch_space = values.LIST_PATCH_SPACE[patch_index]
        parameter_constraint = generator.generate_constraint_for_patch_space(patch_space)
        if parameter_constraint:
            patch_space_constraint = And(patch_formula_extended, parameter_constraint)
    # add patch constraint and user-input->prog-var relationship
    return patch_space_constraint


def select_new_input(argument_list, second_var_list, patch_list=None):
    """
    This function will select a new path for the next concolic execution and generate the inputs that satisfies the path
           log_path : log file for the previous concolic execution that captures PPC
           project_path: project path is the root directory of the program to filter PPC from libraries
    """
    logger.info("generating new input for new path")
    global list_path_explored, list_path_inprogress, count_discovered

    # input_file_byte_list = list()
    # input_file_stat_byte_list = list()

    generated_path_list = values.LIST_GENERATED_PATH
    var_expr_map = reader.collect_symbolic_expression(values.FILE_EXPR_LOG)

    # generated_path_list = generate_new_symbolic_paths(constraint_list)
    # list_path_explored = list(set(list_path_explored + current_path_list))
    selected_patch = None
    patch_constraint = TRUE
    new_path_count = 0

    if oracle.is_loc_in_trace(values.CONF_LOC_PATCH):
        for control_loc, generated_path, ppc_len in generated_path_list:
            path_str = str(generated_path.serialize())
            if path_str not in (list_path_detected + list_path_explored):
                reach_patch_loc = path_str.count("angelic!")
                reach_obs_loc = path_str.count("obs!")
                list_path_inprogress.append((control_loc, generated_path, ppc_len, reach_patch_loc, reach_obs_loc))
                list_path_detected.append(str(generated_path.serialize()))
                new_path_count = new_path_count + 1

    count_discovered = count_discovered + new_path_count
    emitter.highlight("\tidentified " + str(new_path_count) + " new path(s)")
    emitter.highlight("\ttotal discovered: " + str(count_discovered) + " path(s)")
    emitter.highlight("\ttotal remaining: " + str(len(list_path_inprogress)) + " path(s)")
    emitter.highlight("\ttotal infeasible: " + str(len(list_path_infeasible)) + " path(s)")
    if not list_path_inprogress:
        emitter.note("\t\tCount paths explored: " + str(len(list_path_explored)))
        emitter.note("\t\tCount paths remaining: " + str(len(list_path_inprogress)))
        return None, None, patch_list

    patch_constraint = None
    selected_new_path = ""
    selected_control_loc = ""
    if patch_list:
        while not patch_constraint:
            emitter.normal("\tfinding a feasible path for current patch set")
            if not list_path_inprogress:
                emitter.note("\t\tCount paths explored: " + str(len(list_path_explored)))
                emitter.note("\t\tCount paths remaining: " + str(len(list_path_inprogress)))
                return None, None, patch_list
            selected_new_path, selected_control_loc = select_new_path_condition()
            patch_constraint = select_patch_constraint_for_input(patch_list, selected_new_path)
            if patch_constraint:
                list_path_explored.append(str(selected_new_path.serialize()))
                selected_new_path = And(selected_new_path, patch_constraint)
            else:
                list_path_infeasible.append(str(selected_new_path.serialize()))
    else:
        selected_new_path, selected_control_loc = select_new_path_condition()
        list_path_explored.append(str(selected_new_path.serialize()))

    emitter.highlight("\tSelected control location: " + selected_control_loc)
    emitter.highlight("\tSelected path: " + str(selected_new_path))

    input_arg_list, input_var_list = generator.generate_new_input(selected_new_path, argument_list)
    if input_arg_list is None and input_var_list is None:
        return None, None, patch_list
    return input_arg_list, input_var_list, patch_list


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
    emitter.debug("changing directory:" + directory_path)
    project_path = values.CONF_DIR_SRC
    os.chdir(directory_path)
    binary_name = str(program).split("/")[-1]
    input_argument = ""
    # argument_list = str(argument_str).split(" ")
    for argument in argument_list:
        index = list(argument_list).index(argument)
        if "$POC" in argument:
            file_path = values.CONF_PATH_POC
            if values.FILE_POC_GEN:
                file_path = values.FILE_POC_GEN
            concrete_file = open(file_path, 'rb')
            bit_size = os.fstat(concrete_file.fileno()).st_size
            input_argument += " A --sym-files 1 " + str(bit_size) + " "
        elif str(index) in values.CONF_MASK_ARG:
            input_argument += " " + argument
        else:
            input_argument += " --sym-arg " + str(len(str(argument)))
    ktest_path, return_code = generator.generate_ktest(argument_list, second_var_list)
    ktest_log_file = "/tmp/ktest.log"
    ktest_command = "ktest-tool " + ktest_path + " > " + ktest_log_file
    utilities.execute_command(ktest_command)
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
    # hit_location_flag = " "
    runtime_lib_path = definitions.DIRECTORY_LIB + "/libtrident_runtime.bca"
    # if values.CONF_DISTANCE_METRIC == "control-loc":
    hit_location_flag = "--hit-locations " + values.CONF_LOC_BUG + "," + values.CONF_LOC_PATCH + "," + values.CONF_LOC_CRASH + " "
    ppc_log_flag = ""
    if values.CONF_DISTANCE_METRIC != values.OPTIONS_DIST_METRIC[2]:
        ppc_log_flag = "--log-ppc "
    klee_command = "timeout " + str(values.DEFAULT_TIMEOUT_KLEE) + " klee " \
                   "--posix-runtime " \
                   "--libc=uclibc " \
                   "--write-smt2s " \
                   "-allow-seed-extension " \
                   "-named-seed-matching " \
                   "--log-trace " \
                   + "--external-calls=all " \
                   + "--link-llvm-lib={0} " .format(runtime_lib_path) \
                   + "--max-time={0} ".format(values.DEFAULT_TIMEOUT_KLEE) \
                   + "{0}".format(ppc_log_flag) \
                   + "{0}".format(hit_location_flag) \
                   + "--max-forks {0} ".format(values.DEFAULT_MAX_FORK) \
                   + values.CONF_KLEE_FLAGS + " " \
                   + "--seed-out={0} ".format(ktest_path) \
                   + "{0} ".format(binary_name) \
                   + input_argument
    if not print_output:
        klee_command += " > " + File_Log_Path + " 2>&1 "
    return_code = utilities.execute_command(klee_command)
    emitter.debug("changing directory:" + current_dir)
    os.chdir(current_dir)

    # collect artifacts
    ppc_log_path = directory_path + "/klee-last/ppc.log"
    trace_log_path = directory_path + "/klee-last/trace.log"
    if values.CONF_DISTANCE_METRIC != values.OPTIONS_DIST_METRIC[2]:
        values.LIST_PPC, values.LAST_PPC_FORMULA = reader.collect_symbolic_path(ppc_log_path, project_path)
        values.PREFIX_PPC_STR = reader.collect_symbolic_path_prefix(ppc_log_path, project_path)
    else:
        klee_dir_path = directory_path + "/klee-last/"
        values.LAST_PPC_FORMULA = extractor.extract_largest_path_condition(klee_dir_path)
        values.LIST_PPC = generator.generate_ppc_from_formula(values.LAST_PPC_FORMULA)
    values.PREFIX_PPC_FORMULA = generator.generate_formula(values.PREFIX_PPC_STR)
    values.LIST_TRACE = reader.collect_trace(trace_log_path, project_path)
    if oracle.is_loc_in_trace(values.CONF_LOC_BUG) and oracle.is_loc_in_trace(values.CONF_LOC_PATCH):
        if values.CONF_DISTANCE_METRIC != values.OPTIONS_DIST_METRIC[2]:
            values.NEGATED_PPC_FORMULA = generator.generate_path_for_negation()
        else:
            values.NEGATED_PPC_FORMULA = generator.generate_negated_path(values.LAST_PPC_FORMULA)
    else:
        values.NEGATED_PPC_FORMULA = None
    return return_code


def run_symbolic_execution(program, argument_list, print_output=False):
    """
    This function will execute the program in symbolic mode using the initial test case
        program: the absolute path of the bitcode of the program
        argument_list : a list containing each argument in the order that should be fed to the program
    """
    logger.info("running symbolic execution")

    global File_Log_Path
    current_dir = os.getcwd()
    directory_path = "/".join(str(program).split("/")[:-1])
    emitter.debug("changing directory:" + directory_path)
    project_path = values.CONF_PATH_PROJECT
    os.chdir(directory_path)
    binary_name = str(program).split("/")[-1]
    emitter.normal("\texecuting klee in concolic mode")
    runtime_lib_path = definitions.DIRECTORY_LIB + "/libtrident_runtime.bca"
    input_argument = ""
    for argument in argument_list:
        if "$POC" in argument:
            argument = values.CONF_PATH_POC
        input_argument += " " + str(argument)

    klee_command = "/klee/build-origin/bin/klee " \
                   "--posix-runtime " \
                   "--libc=uclibc " \
                   "--write-smt2s " \
                   "--search=dfs " \
                   "-no-exit-on-error " \
                   + "--external-calls=all " \
                   + "--link-llvm-lib={0} " .format(runtime_lib_path) \
                   + "--max-time={0} ".format(values.DEFAULT_TIMEOUT_KLEE_CEGIS) \
                   + "--max-forks {0} ".format(values.DEFAULT_MAX_FORK_CEGIS) \
                   + values.CONF_KLEE_FLAGS + " " \
                   + "{0} ".format(binary_name) \
                   + input_argument

    if not print_output:
        klee_command += " > " + File_Log_Path + " 2>&1 "
    return_code = utilities.execute_command(klee_command)
    emitter.debug("changing directory:" + current_dir)
    os.chdir(current_dir)
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
    emitter.debug("changing directory:" + directory_path)
    os.chdir(directory_path)
    binary_name = str(program).split("/")[-1]
    input_argument = ""
    runtime_lib_path = definitions.DIRECTORY_LIB + "/libtrident_runtime.bca"
    for argument in argument_list:
        if "$POC" in argument:
            argument = values.CONF_PATH_POC
            if values.FILE_POC_GEN:
                argument = values.FILE_POC_GEN
        input_argument += " " + str(argument)
    if output_dir:
        klee_command = "klee --output-dir=" + str(output_dir) + " "
    else:
        klee_command = "klee "
    klee_command += "--posix-runtime " \
                    "--libc=uclibc " \
                    "--write-smt2s " \
                    "--external-calls=all " \
                    "--max-forks {0} ".format(values.DEFAULT_MAX_FORK) \
                    + values.CONF_KLEE_FLAGS + " " \
                    + "--link-llvm-lib={0} ".format(runtime_lib_path) \
                    + "{0} ".format(binary_name) \
                    + input_argument
    if not print_output:
        klee_command += " > " + File_Log_Path + " 2>&1 "
    return_code = utilities.execute_command(klee_command)
    emitter.debug("changing directory:" + current_dir)
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
    global list_path_explored, list_path_inprogress
    run_concolic_execution(program, argument_list, second_var_list, print_output=False)
    is_initial = True
    path_count = 1
    while list_path_inprogress or is_initial:
        is_initial = False
        path_count = path_count + 1
        gen_arg_list, gen_var_list = generator.generate_new_input(argument_list, second_var_list)
        run_concolic_execution(program, gen_arg_list, gen_var_list)

    print("Explored {0} number of paths".format(path_count))


def check_infeasible_paths(patch_list):
    global list_path_inprogress, list_path_infeasible, list_path_detected
    emitter.sub_title("Evaluating Path Pool")
    emitter.normal("\tcomputing infeasibility on remaining paths")
    count = 0
    for path in list_path_inprogress:
        count = count + 1
        emitter.sub_sub_title("Path #" + str(count))
        control_loc, generated_path, ppc_len, reach_patch_loc, reach_obs_loc = path
        feasible_patch_list = select_patch_constraint_for_input(patch_list, generated_path)
        if not feasible_patch_list:
            list_path_infeasible.append(path)
            list_path_inprogress.remove(path)
    emitter.highlight("\ttotal discovered: " + str(len(list_path_detected)) + " path(s)")
    emitter.highlight("\ttotal remaining: " + str(len(list_path_inprogress)) + " path(s)")
    emitter.highlight("\ttotal infeasible: " + str(len(list_path_infeasible)) + " path(s)")
