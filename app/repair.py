import app.configuration
import app.generator
import app.parallel
from app.concolic import run_concolic_execution, select_new_input, check_infeasible_paths, run_concrete_execution
from app.synthesis import load_specification, Program, program_to_code
from pathlib import Path
from typing import List, Dict, Tuple
from pysmt.shortcuts import Not, And, is_sat, write_smtlib, to_smtlib, is_unsat
from app import emitter, values, distance, oracle, parallel, generator, extractor, utilities, concolic, merger, definitions, reader, writer
import time
import sys
import os
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
    emitter.warning("\t[warning] attempting to re-run parallel refinement: missing " + str(len(patch_list) - len(result_list)))

    diff_list_a = get_diff_list(result_list, patch_list)
    result_list_a = parallel.refine_patch_space(diff_list_a, path_condition, assertion)
    recover_list = update_index(result_list_a, diff_list_a, patch_list)
    if len(diff_list_a) != len(result_list_a):
        emitter.error("\t[error] something went wrong with patch validation, attempting to recover")
        emitter.debug("result list size: " + str(len(result_list)))
        emitter.debug("patch list size: " + str(len(patch_list)))
        emitter.warning(
            "\t[warning] attempting to re-run sequential refinement: missing " + str(len(diff_list_a) - len(result_list_a)))
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
        patch_constraint = app.generator.generate_formula_from_patch(patch)
        patch_constraint_str = patch_constraint.serialize()
        patch_index = utilities.get_hash(patch_constraint_str)
        values.LIST_PATCH_SCORE[patch_index] += patch_score
        if is_under_approx is not None:
            current_state = values.LIST_PATCH_UNDERAPPROX_CHECK[patch_index]
            final_state = is_under_approx
            values.LIST_PATCH_UNDERAPPROX_CHECK[patch_index] = final_state
        if is_over_approx is not None:
            current_state = values.LIST_PATCH_OVERAPPROX_CHECK[patch_index]
            final_state = is_over_approx
            values.LIST_PATCH_OVERAPPROX_CHECK[patch_index] = final_state

        if values.DEFAULT_REFINE_METHOD == values.OPTIONS_REFINE_METHOD[3]:
            updated_patch_list.append(patch)
        else:
            if refined_space:
                values.LIST_PATCH_SPACE[patch_index] = refined_space
                updated_patch_list.append(patch)
            else:
                # emitter.debug("Removing Patch", patch_list[index])
                emitter.emit_patch(patch, message="\t\tRemoving Patch: ")

    return updated_patch_list


def reduce(patch_list, path_to_concolic_exec_result, assertion) -> List[Tuple[str, Program]]:  # TODO
    # Reduces the set of patch candidates based on the current path constraint
    # Iterate over patches and check if they still hold based on path constraint.
    path_constraint_file_path = str(path_to_concolic_exec_result) + "/test000001.smt2"
    if not os.path.isfile(path_constraint_file_path):
        return patch_list
    expr_log_path = str(path_to_concolic_exec_result) + "/expr.log"
    path_condition = extractor.extract_formula_from_file(path_constraint_file_path)
    # valid_input_space = parallel.partition_input_space(path_condition, assertion)
    # if valid_input_space:
    #     valid_input_space = merger.merge_space(valid_input_space, path_condition, assertion)
    values.VALID_INPUT_SPACE = None
    count_patches_start = utilities.count_concrete_patches(patch_list)
    if values.DEFAULT_PATCH_TYPE == values.OPTIONS_PATCH_TYPE[1]:
        result_list = parallel.refine_patch_space(patch_list, path_condition, assertion)
    else:
        result_list = parallel.validate_patches_parallel(patch_list, path_condition, assertion)
    updated_patch_list = update_patch_list(result_list, patch_list, path_condition, assertion)
    count_patches_end = utilities.count_concrete_patches(updated_patch_list)
    if values.IS_CRASH and (count_patches_start == count_patches_end):
        emitter.warning("\t[Warning] program crashed, but no patch removed")
    return updated_patch_list


def update_rank_matrix(ranked_patch_list, iteration):
    rank = 0
    for patch in ranked_patch_list:
        rank = rank + 1
        patch_formula = app.generator.generate_formula_from_patch(patch)
        patch_formula_str = patch_formula.serialize()
        patch_index = str(utilities.get_hash(patch_formula_str))
        if patch_index in values.LIST_PATCH_RANKING:
            rank_list = values.LIST_PATCH_RANKING[patch_index]
            rank_list[iteration] = rank
        else:
            rank_list = {iteration: rank}
        values.LIST_PATCH_RANKING[patch_index] = rank_list


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
        patch_formula = app.generator.generate_formula_from_patch(patch)
        patch_formula_str = patch_formula.serialize()
        patch_index = utilities.get_hash(patch_formula_str)
        patch_score = values.LIST_PATCH_SCORE[patch_index]
        concrete_patch_count = 1
        if values.DEFAULT_PATCH_TYPE == values.OPTIONS_PATCH_TYPE[1]:
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
                    concrete_patch_count = utilities.count_concrete_patches_per_template(patch)
        emitter.highlight("\t\tPatch Count: " + str(concrete_patch_count))
        emitter.highlight("\t\tPath Coverage: " + str(patch_score))
        emitter.highlight("\t\tIs Under-approximating: " + str(values.LIST_PATCH_UNDERAPPROX_CHECK[patch_index]))
        emitter.highlight("\t\tIs Over-approximating: " + str(values.LIST_PATCH_OVERAPPROX_CHECK[patch_index]))
        if template_count == values.DEFAULT_PATCH_RANK_LIMIT:
            break


def rank_patches(patch_list):
    filtered_list = []
    # rank first based on coverage
    emitter.normal("\tcomputing rank for each patch")
    for patch in patch_list:
        patch_formula = app.generator.generate_formula_from_patch(patch)
        patch_constraint_str = patch_formula.serialize()
        patch_code_str = ""
        for (lid, prog) in patch.items():
            patch_code_str = lid + ": " + (program_to_code(prog))
        for comp_var, prog_var in values.MAP_PROG_VAR.items():
            patch_code_str = patch_code_str.replace(comp_var, prog_var)
        patch_index = utilities.get_hash(patch_constraint_str)
        patch_score = values.LIST_PATCH_SCORE[patch_index]
        over_approx_score = 10
        if values.LIST_PATCH_OVERAPPROX_CHECK[patch_index]:
            over_approx_score = 0
        under_approx_score = 10
        if values.LIST_PATCH_UNDERAPPROX_CHECK[patch_index]:
            under_approx_score = 0
        patch_len = 10000 - len(patch_constraint_str)
        # if oracle.is_always_true(patch) or oracle.is_always_false(patch):
        #     patch_len = 10000 - 1
        patch_count = 1000 - utilities.count_concrete_patches_per_template(patch)
        filtered_list.append((patch, under_approx_score, over_approx_score, patch_score, patch_count, patch_len))

    ranked_list = sorted(filtered_list, key=operator.itemgetter(3, 1, 2, 4, 5))
    ranked_list.reverse()
    patch_list = numpy.array(ranked_list)[:, 0]
    return list(patch_list)


def run(project_path, program_path):
    emitter.title("Repairing Program")
    ## Generate all possible solutions by running the synthesizer.
    time_check = time.time()
    # satisfied = utilities.check_budget(values.DEFAULT_TIME_DURATION)
    initial_patch_list = generator.generate_patch_set(project_path)
    result_list = parallel.remove_duplicate_patches_parallel(initial_patch_list)
    filtered_patch_list = []
    for result in result_list:
        is_redundant, index = result
        patch = initial_patch_list[index]
        if not is_redundant:
            filtered_patch_list.append(patch)

    index_map = generator.generate_patch_index_map(filtered_patch_list)
    writer.write_as_json(index_map, definitions.FILE_PATCH_RANK_INDEX)
    for patch in filtered_patch_list:
        patch_constraint_str = app.generator.generate_formula_from_patch(patch).serialize()
        patch_index = utilities.get_hash(patch_constraint_str)
        if patch_index in values.LIST_PATCH_SCORE:
            emitter.warning("\tcollision detected in patch score map")
        values.LIST_PATCH_SCORE[patch_index] = 0
        values.LIST_PATCH_OVERAPPROX_CHECK[patch_index] = False
        values.LIST_PATCH_UNDERAPPROX_CHECK[patch_index] = False
        values.LIST_PATCH_SPACE[patch_index] = generator.generate_patch_space(patch)
    emitter.note("\t\t|P|=" + str(utilities.count_concrete_patches(filtered_patch_list)) + ":" + str(len(filtered_patch_list)))
    if values.DEFAULT_PATCH_TYPE == values.OPTIONS_PATCH_TYPE[1]:
        values.COUNT_PATCH_START = utilities.count_concrete_patches(filtered_patch_list)
        values.COUNT_TEMPLATE_START = len(filtered_patch_list)
    else:
        values.COUNT_PATCH_START = len(filtered_patch_list)

    duration = format((time.time() - time_check) / 60, '.3f')
    values.TIME_TO_GENERATE = str(duration)
    definitions.FILE_PATCH_SET = definitions.DIRECTORY_OUTPUT + "/patch-set-gen"
    writer.write_patch_set(filtered_patch_list, definitions.FILE_PATCH_SET)
    if values.CONF_ONLY_GEN:
        return
    if values.DEFAULT_REDUCE_METHOD == "cpr":
        run_cpr(program_path, filtered_patch_list)
    elif values.DEFAULT_REDUCE_METHOD == "cegis":
        run_cegis(program_path, project_path, filtered_patch_list)

    values.COUNT_PATHS_EXPLORED_GEN = len(concolic.list_path_explored)
    values.COUNT_PATHS_DETECTED = len(concolic.list_path_detected)
    values.COUNT_PATHS_SKIPPED = len(concolic.list_path_infeasible)


def run_cegis(program_path, project_path, patch_list):
    test_output_list = values.LIST_TEST_OUTPUT
    test_template = reader.collect_specification(test_output_list[0])
    time_check = time.time()
    assertion, largest_path_condition = concolic.run_concolic_exploration(program_path, patch_list)
    duration = (time.time() - time_check) / 60
    values.TIME_TO_EXPLORE = duration
    emitter.normal("\tcombining explored program paths")
    if not assertion:
        patch = patch_list[0]
        emitter.emit_patch(patch, message="\tfinal patch: ")
        return
    program_specification = generator.generate_program_specification()
    complete_specification = And(Not(assertion), program_specification)
    emitter.normal("\tcomputed the program specification formula")
    emitter.sub_title("Evaluating Patch Pool")
    iteration = 0
    output_dir = definitions.DIRECTORY_OUTPUT
    counter_example_list = []
    time_check = time.time()
    values.CONF_TIME_CHECK = None
    satisfied = utilities.check_budget(values.DEFAULT_TIMEOUT_CEGIS_REFINE)
    patch_generator = generator.generate_patch(project_path, counter_example_list)
    count_throw = 0
    while not satisfied:
        iteration = iteration + 1
        values.ITERATION_NO = iteration
        emitter.sub_sub_title("Iteration: " + str(iteration))
        patch = next(patch_generator, None)
        if not patch:
            emitter.error("[error] cannot generate a patch")
        patch_formula = app.generator.generate_formula_from_patch(patch)
        emitter.emit_patch(patch, message="\tgenerated patch: ")
        patch_formula_extended = generator.generate_extended_patch_formula(patch_formula, largest_path_condition)
        violation_check = And(complete_specification, patch_formula_extended)
        if is_sat(violation_check):
            model = generator.generate_model(violation_check)
            # print(model)
            arg_list = values.ARGUMENT_LIST
            poc_path = values.CONF_PATH_POC
            values.FILE_POC_GEN = definitions.DIRECTORY_OUTPUT + "/violation-" + str(values.ITERATION_NO)
            gen_path = values.FILE_POC_GEN
            input_arg_list, input_var_list = generator.generate_new_input(violation_check, arg_list, poc_path, gen_path)
            klee_out_dir = output_dir + "/klee-out-repair-" + str(iteration)
            klee_test_file = output_dir + "/klee-test-" + str(iteration)
            exit_code = concolic.run_concrete_execution(program_path + ".bc", input_arg_list, True, klee_out_dir)
            # assert exit_code == 0
            values.COUNT_PATHS_EXPLORED = values.COUNT_PATHS_EXPLORED + 1
            emitter.normal("\t\tgenerating new assertion")
            test_assertion, count_obs = generator.generate_assertion(test_template, klee_out_dir)
            write_smtlib(test_assertion, klee_test_file)
            counter_example_list.append((klee_test_file, klee_out_dir))
            emitter.highlight("\t\tnew counter-example added")
            patch = None
            emitter.highlight("\t\tremoving current patch")
            count_throw = count_throw + 1
        else:
            klee_test_file = output_dir + "/klee-test-FINAL"
            # print(to_smtlib(violation_check, False))
            write_smtlib(violation_check, klee_test_file)
            break
        satisfied = utilities.check_budget(values.DEFAULT_TIMEOUT_CEGIS_REFINE)
        if satisfied:
            emitter.warning("\t[warning] ending due to timeout of " + str(values.DEFAULT_TIMEOUT_CEGIS_REFINE) + " minutes")
    duration = (time.time() - time_check) / 60
    values.TIME_TO_REDUCE = duration
    # patch_list = [patch]
    # definitions.FILE_PATCH_SET = definitions.DIRECTORY_OUTPUT + "/patch-set-cegis"
    # writer.write_patch_set(patch_list, definitions.FILE_PATCH_SET)
    # patch = next(patch_generator, None)
    # while patch is not None:
    #     patch_formula = app.generator.generate_formula_from_patch(patch)
    #     patch_formula_extended = generator.generate_extended_patch_formula(patch_formula, largest_path_condition)
    #     violation_check = And(complete_specification, patch_formula_extended)
    #     if is_unsat(violation_check):
    #         count_final = count_final + 1
    #     patch = next(patch_generator, None)
    emitter.emit_patch(patch, message="\tfinal patch: ")
    values.COUNT_PATCH_END = values.COUNT_PATCH_START - count_throw


def compute_iteration_stat(patch_list, iteration):
    ranked_patch_list = rank_patches(patch_list)
    update_rank_matrix(ranked_patch_list, iteration)
    definitions.FILE_PATCH_SET = definitions.DIRECTORY_OUTPUT + "/patch-set-ranked-" + str(iteration)
    writer.write_patch_set(ranked_patch_list, definitions.FILE_PATCH_SET)
    writer.write_as_json(values.LIST_PATCH_RANKING, definitions.FILE_PATCH_RANK_MATRIX)
    if values.DEFAULT_PATCH_TYPE == values.OPTIONS_PATCH_TYPE[1]:
        values.COUNT_PATCH_END = utilities.count_concrete_patches(ranked_patch_list)
        values.COUNT_TEMPLATE_END = len(patch_list)
    else:
        values.COUNT_PATCH_END = len(ranked_patch_list)


def run_cpr(program_path, patch_list):
    emitter.sub_title("Evaluating Patch Pool")
    values.CONF_TIME_CHECK = None
    satisfied = utilities.check_budget(values.DEFAULT_TIME_DURATION)
    if satisfied:
        emitter.warning("\t[warning] ending due to timeout of " + str(values.DEFAULT_TIME_DURATION) + " minutes")
    iteration = 0
    assertion_template = values.SPECIFICATION_TXT
    test_input_list = values.LIST_TEST_INPUT
    count_seeds = len(values.LIST_SEED_INPUT)
    count_inputs = len(test_input_list)
    count_fail_inputs = count_inputs - count_seeds
    while not satisfied and len(patch_list) > 0:
        if iteration == 0:
            seed_id = 0
            for argument_list in test_input_list:
                seed_id = seed_id + 1
                # if seed_id not in values.USEFUL_SEED_ID_LIST:
                #     continue
                time_check = time.time()
                poc_path = None
                iteration = iteration + 1
                values.ITERATION_NO = iteration
                output_dir_path = definitions.DIRECTORY_OUTPUT
                klee_test_dir = output_dir_path + "/klee-out-test-" + str(iteration-1)
                klee_out_dir = output_dir_path + "/klee-out-repair-" + str(iteration - 1)
                argument_list = app.configuration.extract_input_arg_list(argument_list)
                generalized_arg_list = []
                for arg in argument_list:
                    if str(argument_list.index(arg)) in values.CONF_MASK_ARG:
                        generalized_arg_list.append(arg)
                    elif arg in (list(values.LIST_SEED_FILES.values()) + list(values.LIST_TEST_FILES.values())):
                        poc_path = arg
                        values.FILE_POC_SEED = arg
                        values.FILE_POC_GEN = arg
                        generalized_arg_list.append("$POC")
                    else:
                        generalized_arg_list.append(arg)
                emitter.sub_sub_title("Iteration: " + str(iteration) + " - Using Seed #" + str(seed_id))
                emitter.highlight("\tUsing Arguments: " + str(generalized_arg_list))
                emitter.highlight("\tUsing Input File: " + str(poc_path))
                if values.LIST_TEST_BINARY:
                    program_path = values.LIST_TEST_BINARY[iteration-1]
                    values.CONF_PATH_PROGRAM = program_path
                else:
                    program_path = values.CONF_PATH_PROGRAM
                emitter.highlight("\tUsing Binary: " + str(program_path))
                extractor.extract_byte_code(program_path)
                if not os.path.isfile(program_path + ".bc"):
                    app.utilities.error_exit("Unable to generate bytecode for " + program_path)

                if seed_id > count_fail_inputs:
                    exit_code = run_concrete_execution(program_path + ".bc", argument_list, True, klee_test_dir)
                    assert exit_code == 0
                    # set location of bug/crash
                    values.IS_CRASH = False
                    latest_crash_loc = reader.collect_crash_point(values.FILE_MESSAGE_LOG)
                    if not oracle.is_loc_in_trace(values.CONF_LOC_PATCH):
                        continue
                    if latest_crash_loc:
                        values.IS_CRASH = True
                        emitter.success("\t\t\t[info] identified a crash location: " + str(latest_crash_loc))
                        if latest_crash_loc not in values.CONF_LOC_LIST_CRASH:
                            values.CONF_LOC_LIST_CRASH.append(latest_crash_loc)

                values.ARGUMENT_LIST = generalized_arg_list

                _, second_var_list = generator.generate_angelic_val(klee_test_dir, generalized_arg_list, poc_path)
                exit_code = run_concolic_execution(program_path + ".bc", generalized_arg_list, second_var_list, True, klee_out_dir)
                # assert exit_code == 0
                duration = (time.time() - time_check) / 60
                values.TIME_TO_EXPLORE = values.TIME_TO_EXPLORE + duration
                values.COUNT_PATHS_EXPLORED = values.COUNT_PATHS_EXPLORED + 1
                generated_path_list = app.parallel.generate_symbolic_paths(values.LIST_PPC, generalized_arg_list, poc_path, program_path)
                if generated_path_list:
                    values.LIST_GENERATED_PATH = generated_path_list + values.LIST_GENERATED_PATH
                values.LIST_PPC = []

                # check if new path hits patch location / fault location
                gen_masked_byte_list = generator.generate_mask_bytes(klee_out_dir, poc_path)
                if values.FILE_POC_SEED not in values.MASK_BYTE_LIST:
                    values.MASK_BYTE_LIST[values.FILE_POC_SEED] = gen_masked_byte_list
                else:
                    current_mask_list = values.MASK_BYTE_LIST[values.FILE_POC_SEED]
                    values.MASK_BYTE_LIST[values.FILE_POC_SEED] = sorted(
                        list(set(current_mask_list + gen_masked_byte_list)))
                distance.update_distance_map()
                if not oracle.is_loc_in_trace(values.CONF_LOC_PATCH):
                    continue
                if not values.SPECIFICATION_TXT and not oracle.is_loc_in_trace(values.CONF_LOC_BUG):
                    continue
                time_check = time.time()
                assertion, count_obs = generator.generate_assertion(assertion_template,
                                                                    Path(klee_out_dir).resolve())
                # print(assertion.serialize())
                patch_list = reduce(patch_list, Path(klee_out_dir).resolve(), assertion)
                emitter.note("\t\t|P|=" + str(utilities.count_concrete_patches(patch_list)) + ":" + str(len(patch_list)))
                duration = (time.time() - time_check) / 60
                emitter.note("\t\treduce finished in " + str(format(duration, '.3f')) + " minutes")
                values.TIME_TO_REDUCE = values.TIME_TO_REDUCE + duration
                values.COUNT_TEMPLATE_END_SEED = len(patch_list)
                values.COUNT_PATCH_END_SEED = utilities.count_concrete_patches(patch_list)
                satisfied = utilities.check_budget(values.DEFAULT_TIME_DURATION)

                if satisfied:
                    emitter.warning(
                        "\t[warning] ending due to timeout of " + str(values.DEFAULT_TIME_DURATION) + " minutes")
                    break
                compute_iteration_stat(patch_list, iteration)

            emitter.success("\t\tend of concolic exploration using user-provided seeds")
            # emitter.success("\t\t\t|P|=" + str(values.COUNT_PATCH_END_SEED) + ":" + str(values.COUNT_TEMPLATE_END_SEED))


        else:
            iteration = iteration + 1
            values.ITERATION_NO = iteration
            emitter.sub_sub_title("Iteration: " + str(iteration))
            time_check = time.time()
            argument_list = values.ARGUMENT_LIST
            second_var_list = values.SECOND_VAR_LIST
            output_dir_path = definitions.DIRECTORY_OUTPUT
            klee_out_dir = output_dir_path + "/klee-out-repair-" + str(iteration - 1)
            # if oracle.is_loc_in_trace(values.CONF_LOC_PATCH):
            gen_arg_list, gen_var_list, patch_list, argument_list, poc_path, program_path = select_new_input(patch_list)
            emitter.highlight("\tUsing Arguments: " + str(gen_arg_list))
            emitter.highlight("\tUsing Input File: " + str(poc_path))
            emitter.highlight("\tUsing Binary: " + str(program_path))
            if not patch_list:
                emitter.warning("\t\t[warning] unable to generate a patch")
                break
            elif not gen_arg_list and not gen_var_list:
                emitter.warning("\t\t[warning] no more paths to generate new input")
                break
            assert gen_arg_list  # there should be a concrete input
            # print(">> new input: " + str(gen_arg_list))

            ## Concolic execution of concrete input and patch candidate to retrieve path constraint.
            exit_code = run_concolic_execution(program_path + ".bc", gen_arg_list, gen_var_list, False, klee_out_dir)
            # assert exit_code == 0
            duration = (time.time() - time_check) / 60
            values.COUNT_PATHS_EXPLORED = values.COUNT_PATHS_EXPLORED + 1
            values.TIME_TO_EXPLORE = values.TIME_TO_EXPLORE + duration
            # Checks for the current coverage.
            satisfied = utilities.check_budget(values.DEFAULT_TIME_DURATION)
            time_check = time.time()
            values.LIST_GENERATED_PATH = app.parallel.generate_symbolic_paths(values.LIST_PPC, argument_list, poc_path, program_path)
            values.LIST_PPC = []
            # check if new path hits patch location / fault location
            if not oracle.is_loc_in_trace(values.CONF_LOC_PATCH):
                continue
            if not values.SPECIFICATION_TXT and not oracle.is_loc_in_trace(values.CONF_LOC_BUG):
                continue
            distance.update_distance_map()
            ## Reduces the set of patch candidates based on the current path constraint
            assertion, count_obs = generator.generate_assertion(assertion_template, Path(klee_out_dir).resolve())
            # print(assertion.serialize())
            patch_list = reduce(patch_list, Path(klee_out_dir).resolve(), assertion)
            emitter.note("\t\t|P|=" + str(utilities.count_concrete_patches(patch_list)) + ":" + str(len(patch_list)))
            duration = (time.time() - time_check) / 60
            emitter.note("\t\treduce finished in " + str(format(duration, '.3f')) + " minutes")
            values.TIME_TO_REDUCE = values.TIME_TO_REDUCE + duration
            if satisfied:
                emitter.warning("\t[warning] ending due to timeout of " + str(values.DEFAULT_TIME_DURATION) + " minutes")

            compute_iteration_stat(patch_list, iteration)

    if not patch_list:
        values.COUNT_PATCH_END = len(patch_list)
        emitter.warning("\t\t[warning] unable to generate a patch")
    else:
        definitions.FILE_PATCH_SET = definitions.DIRECTORY_OUTPUT + "/patch-set-original"
        writer.write_patch_set(patch_list, definitions.FILE_PATCH_SET)
        ranked_patch_list = rank_patches(patch_list)
        print_patch_list(ranked_patch_list)
        definitions.FILE_PATCH_SET = definitions.DIRECTORY_OUTPUT + "/patch-set-ranked"
        writer.write_patch_set(ranked_patch_list, definitions.FILE_PATCH_SET)
        if values.DEFAULT_COLLECT_STAT:
            check_infeasible_paths(patch_list)
        if values.DEFAULT_PATCH_TYPE == values.OPTIONS_PATCH_TYPE[1]:
            values.COUNT_PATCH_END = utilities.count_concrete_patches(ranked_patch_list)
            values.COUNT_TEMPLATE_END = len(patch_list)
        else:
            values.COUNT_PATCH_END = len(ranked_patch_list)



