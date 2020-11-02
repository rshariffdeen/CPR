from main.concolic import run_concolic_execution, select_new_input
from main.synthesis import load_specification, Program
from pathlib import Path
from typing import List, Dict, Tuple
from pysmt.shortcuts import Not
from main import emitter, values, distance, oracle, parallel, generator, extractor, utilities, concolic, merger
import time
import sys
import operator
import numpy


def get_diff_list(result_list, patch_list):
    filtered_list = []
    diff_list = patch_list.copy()
    for result in result_list:
        refined_space, index, patch_score, is_under_approx, is_over_approx = result
        patch = patch_list[index]
        filtered_list.append(patch)
        diff_list.remove(patch)
    return diff_list


def update_index(result_list, patch_list_new, patch_list_old):
    updated_list = []
    for result in result_list:
        refined_space, index, patch_score, is_under_approx, is_over_approx = result
        patch = patch_list_new[index]
        new_index = patch_list_old.index(patch)
        updated_list.append((refined_space, new_index, patch_score, is_under_approx, is_over_approx))
    return updated_list


def recover_patch_list(result_list, patch_list, path_condition, assertion):
    recover_list = []
    emitter.error("\t[error] something went wrong with patch validation, attempting to recover")
    emitter.debug("result list size: " + str(len(result_list)))
    emitter.debug("patch list size: " + str(len(patch_list)))
    emitter.warning("\t[warning] attempting to re-run parallel refinement: " + str(len(patch_list) - len(result_list)))

    diff_list_a = get_diff_list(result_list, patch_list)
    result_list_a = parallel.refine_patch_space(diff_list_a, path_condition, assertion)
    recover_list = update_index(result_list_a, diff_list_a, patch_list)
    if len(diff_list_a) != len(result_list_a):
        emitter.error("\t[error] something went wrong with patch validation, attempting to recover")
        emitter.debug("result list size: " + str(len(result_list)))
        emitter.debug("patch list size: " + str(len(patch_list)))
        emitter.warning(
            "\t[warning] attempting to re-run sequential refinement: " + str(len(diff_list_a) - len(result_list_a)))
        diff_list_b = get_diff_list(result_list_a, diff_list_a)
        result_list_b = parallel.refine_patch_space(diff_list_b, path_condition, assertion, True)
        recover_list = recover_list + update_index(result_list_b, diff_list_b, patch_list)
    return recover_list


def update_patch_list(result_list, patch_list, path_condition, assertion):
    updated_patch_list = []
    if len(result_list) != len(patch_list):
        recover_list = recover_patch_list(result_list, patch_list, path_condition, assertion)
        result_list = result_list + recover_list
    for result in result_list:
        refined_space, index, patch_score, is_under_approx, is_over_approx = result
        patch = patch_list[index]
        patch_constraint = extractor.extract_formula_from_patch(patch)
        patch_constraint_str = patch_constraint.serialize()
        patch_index = utilities.get_hash(patch_constraint_str)
        values.LIST_PATCH_SCORE[patch_index] += patch_score
        if is_under_approx is not None:
            values.LIST_PATCH_UNDERAPPROX_CHECK[patch_index] = is_under_approx
        if is_over_approx is not None:
            values.LIST_PATCH_OVERAPPROX_CHECK[patch_index] = is_over_approx

        if values.CONF_REFINE_METHOD == values.OPTIONS_REFINE_METHOD[3]:
            updated_patch_list.append(patch)
        else:
            if refined_space:
                values.LIST_PATCH_SPACE[patch_index] = refined_space
                updated_patch_list.append(patch)
            else:
                # emitter.debug("Removing Patch", patch_list[index])
                emitter.emit_patch(patch, message="\t\tRemoving Patch: ")

    return updated_patch_list


def reduce(patch_list: List[Dict[str, Program]], path_to_concolic_exec_result: str,
           assertion) -> List[Tuple[str, Program]]:  # TODO
    # Reduces the set of patch candidates based on the current path constraint
    # Iterate over patches and check if they still hold based on path constraint.
    emitter.normal("\tupdating patch pool")
    path_constraint_file_path = str(path_to_concolic_exec_result) + "/test000001.smt2"
    expr_log_path = str(path_to_concolic_exec_result) + "/expr.log"
    path_condition = extractor.extract_assertion(path_constraint_file_path)
    valid_input_space = parallel.partition_input_space(path_condition, assertion)
    if valid_input_space:
        valid_input_space = merger.merge_space(valid_input_space, path_condition, assertion)
    values.VALID_INPUT_SPACE = valid_input_space
    if values.CONF_PATCH_TYPE == values.OPTIONS_PATCH_TYPE[1]:
        result_list = parallel.refine_patch_space(patch_list, path_condition, assertion)
    else:
        result_list = parallel.validate_patches_parallel(patch_list, path_condition, assertion)
    updated_patch_list = update_patch_list(result_list, patch_list, path_condition, assertion)
    return updated_patch_list


def print_patch_list(patch_list):
    template_count = 0
    emitter.sub_title("List of Top " + str(values.DEFAULT_PATCH_RANK_LIMIT) + " Correct Patches")
    if not patch_list:
        emitter.warning("\t[warning] unable to generate any patch")
        return
    for patch in patch_list:
        template_count = template_count + 1
        emitter.sub_sub_title("Patch #" + str(template_count))
        emitter.emit_patch(patch, message="\t\t")
        concrete_patch_count = 1
        patch_formula = extractor.extract_formula_from_patch(patch)
        patch_formula_str = patch_formula.serialize()
        patch_index = utilities.get_hash(patch_formula_str)
        patch_score = values.LIST_PATCH_SCORE[patch_index]
        if values.CONF_PATCH_TYPE == values.OPTIONS_PATCH_TYPE[1]:
            patch_space = values.LIST_PATCH_SPACE[patch_index]
            partition_count = 0
            for partition in patch_space:
                partition_count = partition_count + 1
                emitter.highlight("\t\tPartition: " + str(partition_count))
                for constant_name in partition:
                    emitter.highlight("\t\t\tConstant: " + constant_name)
                    constant_info = partition[constant_name]
                    lower_bound = str(constant_info['lower-bound'])
                    upper_bound = str(constant_info['upper-bound'])
                    emitter.highlight("\t\t\tRange: " + lower_bound + " <= " + constant_name + " <= " + upper_bound)
                    dimension = len(range(int(lower_bound), int(upper_bound) + 1))
                    emitter.highlight("\t\t\tDimension: " + str(dimension))
                    concrete_patch_count = concrete_patch_count * dimension
        emitter.highlight("\t\tPatch Count: " + str(concrete_patch_count))
        emitter.highlight("\t\tPath Coverage: " + str(patch_score))
        emitter.highlight("\t\tIs Under-approximating: " + str(values.LIST_PATCH_UNDERAPPROX_CHECK[patch_index]))
        emitter.highlight("\t\tIs Over-approximating: " + str(values.LIST_PATCH_OVERAPPROX_CHECK[patch_index]))
        if template_count == values.DEFAULT_PATCH_RANK_LIMIT:
            break


def count_concrete_patches_per_template(abstract_patch):
    if values.CONF_PATCH_TYPE == values.OPTIONS_PATCH_TYPE[0]:
        return 1
    patch_formula = extractor.extract_formula_from_patch(abstract_patch)
    patch_formula_str = patch_formula.serialize()
    patch_index = utilities.get_hash(patch_formula_str)
    patch_space = values.LIST_PATCH_SPACE[patch_index]
    total_concrete_count = 0

    if patch_space:
        for partition in patch_space:
            partition_concrete_count = 1
            for parameter_name in partition:
                constraint_info = partition[parameter_name]
                lower_bound = str(constraint_info['lower-bound'])
                upper_bound = str(constraint_info['upper-bound'])
                parameter_dimension = len(range(int(lower_bound), int(upper_bound) + 1))
                partition_concrete_count = partition_concrete_count * parameter_dimension
            total_concrete_count = total_concrete_count + partition_concrete_count
    return total_concrete_count


def count_concrete_patches(patch_list):
    patch_count = 0
    for abstract_patch in patch_list:
        concrete_count = count_concrete_patches_per_template(abstract_patch)
        patch_count = patch_count + concrete_count
    return patch_count


def rank_patches(patch_list):
    filtered_list = []
    # rank first based on coverage
    for patch in patch_list:
        patch_constraint_str = extractor.extract_formula_from_patch(patch).serialize()
        patch_index = utilities.get_hash(patch_constraint_str)
        patch_score = values.LIST_PATCH_SCORE[patch_index]
        is_over_approx = 1 - values.LIST_PATCH_OVERAPPROX_CHECK[patch_index]
        is_under_approx = 1 - values.LIST_PATCH_UNDERAPPROX_CHECK[patch_index]
        patch_len = 10000 - len(patch_constraint_str)
        patch_count = len(range(values.DEFAULT_PATCH_LOWER_BOUND, values.DEFAULT_PATCH_UPPER_BOUND)) - count_concrete_patches_per_template(patch)
        filtered_list.append((patch, is_under_approx, is_over_approx, patch_score, patch_count, patch_len))

    ranked_list = sorted(filtered_list, key=operator.itemgetter(1, 2, 3, 4, 5))
    ranked_list.reverse()
    patch_list = numpy.array(ranked_list)[:, 0]
    return list(patch_list)


def run(project_path, program_path):
    emitter.title("Repairing Program")
    ## Generate all possible solutions by running the synthesizer.
    emitter.note("\tconfiguration.is_crash:" + str(values.IS_CRASH))
    emitter.note("\tconfiguration.assertion:" + str(values.SPECIFICATION_TXT[1]))
    emitter.note("\tconfiguration.generation_limit:" + str(values.DEFAULT_GEN_SEARCH_LIMIT))
    emitter.note("\tconfiguration.max_bound:" + str(values.DEFAULT_PATCH_UPPER_BOUND))
    emitter.note("\tconfiguration.low_bound:" + str(values.DEFAULT_PATCH_LOWER_BOUND))
    emitter.note("\tconfiguration.stack_size:" + str(sys.getrecursionlimit()))
    emitter.note("\tconfiguration.refine_strategy:" + str(values.CONF_REFINE_METHOD))
    time_check = time.time()
    patch_list = generator.generate_patch_set(project_path)
    for patch in patch_list:
        patch_constraint_str = extractor.extract_formula_from_patch(patch).serialize()
        patch_index = utilities.get_hash(patch_constraint_str)
        if patch_index in values.LIST_PATCH_SCORE:
            emitter.warning("\tcollision detected in patch score map")
        values.LIST_PATCH_SCORE[patch_index] = 0
        values.LIST_PATCH_OVERAPPROX_CHECK[patch_index] = 0
        values.LIST_PATCH_UNDERAPPROX_CHECK[patch_index] = 0
        values.LIST_PATCH_SPACE[patch_index] = generator.generate_patch_space(patch)

    if values.CONF_PATCH_TYPE == values.OPTIONS_PATCH_TYPE[1]:
        values.COUNT_PATCH_START = count_concrete_patches(patch_list)
        values.COUNT_TEMPLATE_START = len(patch_list)
    else:
        values.COUNT_PATCH_START = len(patch_list)

    duration = format((time.time() - time_check) / 60, '.3f')
    values.TIME_TO_GENERATE = str(duration)

    if values.CONF_REDUCE_METHOD == "fitreduce":
        run_fitreduce(program_path, patch_list)
    elif values.CONF_REDUCE_METHOD == "cegis":
        run_cegis(program_path, patch_list)


def run_cegis(program_path, patch_list):
    emitter.sub_title("Evaluating Patch Pool")
    satisfied = len(patch_list) <= 1
    iteration = 0
    assertion = values.SPECIFICATION
    test_output_list = values.CONF_TEST_OUTPUT
    binary_dir_path = "/".join(program_path.split("/")[:-1])
    while not satisfied and len(patch_list) > 0:
        iteration = iteration + 1
        values.ITERATION_NO = iteration
        emitter.sub_sub_title("Iteration: " + str(iteration))
        ## Pick new input and patch candidate for next concolic execution step.
        argument_list = values.ARGUMENT_LIST
        second_var_list = values.SECOND_VAR_LIST
        if oracle.is_loc_in_trace(values.CONF_LOC_PATCH):
            values.LIST_GENERATED_PATH = generator.generate_symbolic_paths(values.LIST_PPC)
        gen_arg_list, gen_var_list, P = select_new_input(argument_list, second_var_list,
                                                         P)  # TODO (later) patch candidate missing
        if not P:
            emitter.warning("\t\t[warning] unable to generate a patch")
            break
        elif not gen_arg_list and not gen_var_list:
            emitter.warning("\t\t[warning] no more paths to generate new input")
            break
        assert gen_arg_list  # there should be a concrete input
        # print(">> new input: " + str(gen_arg_list))

        ## Concolic execution of concrete input and patch candidate to retrieve path constraint.
        exit_code = run_concolic_execution(program_path + ".bc", gen_arg_list, gen_var_list)
        assert exit_code == 0

        # Checks for the current coverage.
        satisfied = utilities.check_budget()

        # check if new path hits patch location / fault location
        if not oracle.is_loc_in_trace(values.CONF_LOC_PATCH):
            continue
        if not values.IS_CRASH and not oracle.is_loc_in_trace(values.CONF_LOC_BUG):
            continue

        distance.update_distance_map()
        ## Reduces the set of patch candidates based on the current path constraint
        P = reduce(P, Path(binary_dir_path + "/klee-last/").resolve(), assertion)
        emitter.note("\t\t|P|=" + str(len(P)))

    if not patch_list:
        values.COUNT_PATCH_END = len(patch_list)
        emitter.warning("\t\t[warning] unable to generate a patch")
    else:
        print_patch_list(patch_list)
        if values.CONF_PATCH_TYPE == values.OPTIONS_PATCH_TYPE[1]:
            values.COUNT_PATCH_END = count_concrete_patches(patch_list)
            values.COUNT_TEMPLATE_END = len(patch_list)
        else:
            values.COUNT_PATCH_END = len(patch_list)


def run_fitreduce(program_path, patch_list):
    emitter.sub_title("Evaluating Patch Pool")
    satisfied = len(patch_list) <= 1
    iteration = 0
    assertion_template = values.SPECIFICATION
    test_output_list = values.CONF_TEST_OUTPUT
    binary_dir_path = "/".join(program_path.split("/")[:-1])

    while not satisfied and len(patch_list) > 0:
        iteration = iteration + 1
        values.ITERATION_NO = iteration
        emitter.sub_sub_title("Iteration: " + str(iteration))
        ## Pick new input and patch candidate for next concolic execution step.
        argument_list = values.ARGUMENT_LIST
        second_var_list = values.SECOND_VAR_LIST
        if oracle.is_loc_in_trace(values.CONF_LOC_PATCH):
            values.LIST_GENERATED_PATH = generator.generate_symbolic_paths(values.LIST_PPC)
        gen_arg_list, gen_var_list, patch_list = select_new_input(argument_list, second_var_list, patch_list)  # TODO (later) patch candidate missing
        if not patch_list:
            emitter.warning("\t\t[warning] unable to generate a patch")
            break
        elif not gen_arg_list and not gen_var_list:
            emitter.warning("\t\t[warning] no more paths to generate new input")
            break
        assert gen_arg_list  # there should be a concrete input
        # print(">> new input: " + str(gen_arg_list))

        ## Concolic execution of concrete input and patch candidate to retrieve path constraint.
        exit_code = run_concolic_execution(program_path + ".bc", gen_arg_list, gen_var_list)
        assert exit_code == 0

        # Checks for the current coverage.
        satisfied = utilities.check_budget()

        # check if new path hits patch location / fault location
        if not oracle.is_loc_in_trace(values.CONF_LOC_PATCH):
            continue
        if not values.IS_CRASH and not oracle.is_loc_in_trace(values.CONF_LOC_BUG):
            continue

        distance.update_distance_map()
        ## Reduces the set of patch candidates based on the current path constraint
        assertion = generator.generate_assertion(assertion_template,Path(binary_dir_path + "/klee-last/").resolve())
        print(assertion.serialize())
        patch_list = reduce(patch_list, Path(binary_dir_path + "/klee-last/").resolve(), assertion)
        emitter.note("\t\t|P|=" + str(len(patch_list)))

    if not patch_list:
        values.COUNT_PATCH_END = len(patch_list)
        emitter.warning("\t\t[warning] unable to generate a patch")
    else:
        ranked_patch_list = rank_patches(patch_list)
        print_patch_list(ranked_patch_list)
        if values.CONF_PATCH_TYPE == values.OPTIONS_PATCH_TYPE[1]:
            values.COUNT_PATCH_END = count_concrete_patches(ranked_patch_list)
            values.COUNT_TEMPLATE_END = len(patch_list)
        else:
            values.COUNT_PATCH_END = len(ranked_patch_list)


def concolic_exploration(program_path):
    while not satisfied and len(patch_list) > 1:
        patch_list = values.LIST_PATCHES
        iteration = iteration + 1
        values.ITERATION_NO = iteration
        emitter.sub_sub_title("Iteration: " + str(iteration))

        ## Pick new input and patch candidate for next concolic execution step.
        argument_list = values.ARGUMENT_LIST
        second_var_list = values.SECOND_VAR_LIST
        if oracle.is_loc_in_trace(values.CONF_LOC_PATCH):
            values.LIST_GENERATED_PATH = generator.generate_symbolic_paths(values.LIST_PPC)
        gen_arg_list, gen_var_list, patch_list = concolic.select_new_input(argument_list, second_var_list,
                                                                           patch_list)  # TODO (later) patch candidate missing

        if not patch_list:
            emitter.warning("\t\t[warning] unable to generate a patch")
            break
        elif not gen_arg_list and not gen_var_list:
            emitter.warning("\t\t[warning] no more paths to generate new input")
            break
        assert gen_arg_list  # there should be a concrete input
        # print(">> new input: " + str(gen_arg_list))

        ## Concolic execution of concrete input and patch candidate to retrieve path constraint.
        exit_code = concolic.run_concolic_execution(program_path + ".bc", gen_arg_list, gen_var_list)
        assert exit_code == 0

        # Checks for the current coverage.
        satisfied = utilities.check_budget()

        # check if new path hits patch location / fault location
        if not oracle.is_loc_in_trace(values.CONF_LOC_PATCH):
            continue
        if not values.IS_CRASH and not oracle.is_loc_in_trace(values.CONF_LOC_BUG):
            continue
        distance.update_distance_map()
