from main.concolic import run_concolic_execution, generate_new_input
from main.synthesis import load_specification, synthesize, Program
from pathlib import Path
from typing import List, Dict, Tuple
from main import emitter, values, distance, oracle, parallel, generator
import time


check_counter = 1


def reduce(patch_list: List[Dict[str, Program]], path_to_concolic_exec_result: str,
           assertion) -> List[Tuple[str, Program]]:  # TODO
    # Reduces the set of patch candidates based on the current path constraint
    # Iterate over patches and check if they still hold based on path constraint.
    emitter.normal("\tupdating patch pool")
    updated_patch_set = []
    result_list = parallel.validate_patches_parallel(patch_list, path_to_concolic_exec_result, assertion)
    for result in result_list:
        is_valid, index = result
        if is_valid:
            updated_patch_set.append(patch_list[index])
        else:
            # emitter.debug("Removing Patch", patch_list[index])
            emitter.emit_patch(patch_list[index], message="\t\tRemoving Patch: ")

    return updated_patch_set


def check_coverage():  # TODO
    global check_counter
    if check_counter < values.DEFAULT_ITERATION_LIMIT:  # Only for testing purpose.
        check_counter += 1
        return False
    else:
        return True


def print_patch_list(patch_list):
    count = 0
    emitter.sub_title("List of Synthesised Patches")
    if not patch_list:
        emitter.warning("\t[warning] unable to generate any patch")
        return
    for patch in patch_list:
        count = count + 1
        emitter.sub_sub_title("Patch #" + str(count))

        emitter.emit_patch(patch, message="\t\t")


def run(project_path, program_path):
    emitter.title("Repairing Program")
    ## Generate all possible solutions by running the synthesizer.

    emitter.debug("\tconfiguration.is_crash:" + str(values.IS_CRASH))
    emitter.debug("\tconfiguration.assertion:" + str(values.SPECIFICATION))
    emitter.debug("\tconfiguration.generation_limit:" + str(values.DEFAULT_GEN_SEARCH_LIMIT))
    emitter.debug("\tconfiguration.max_bound:" + str(values.CONF_MAX_BOUND))
    emitter.debug("\tconfiguration.low_bound:" + str(values.CONF_LOW_BOUND))

    time_check = time.time()
    P = generator.generate_patch_set(project_path)
    values.TIME_TO_GENERATE = str(time.time() - time_check)
    emitter.sub_title("Evaluating Patch Pool")
    satisfied = len(P) <= 1
    iteration = 0
    assertion = values.SPECIFICATION
    test_output_list = values.CONF_TEST_OUTPUT
    binary_dir_path = "/".join(program_path.split("/")[:-1])

    while not satisfied and len(P) > 1:
        iteration = iteration + 1
        values.ITERATION_NO = iteration
        emitter.sub_sub_title("Iteration: " + str(iteration))
        ## Pick new input and patch candidate for next concolic execution step.
        argument_list = values.ARGUMENT_LIST
        second_var_list = values.SECOND_VAR_LIST
        gen_arg_list, gen_var_list, P = generate_new_input(argument_list, second_var_list, P)  # TODO (later) patch candidate missing
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
        satisfied = check_coverage()

        # check if new path hits patch location / fault location
        if not oracle.is_loc_in_trace(values.CONF_LOC_PATCH):
            continue
        if not values.IS_CRASH and not oracle.is_loc_in_trace(values.CONF_LOC_BUG):
            continue

        distance.update_distance_map()
        ## Reduces the set of patch candidates based on the current path constraint
        P = reduce(P, Path(binary_dir_path + "/klee-last/").resolve(), assertion)
        emitter.debug("|P|=", str(len(P)))

    print_patch_list(P)
