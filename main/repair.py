import subprocess
import os
import sys
import random

sys.path.append('/concolic-repair/main')
from concolic import generate_ktest, run_concolic_execution, run_concrete_execution, generate_new_input
from main.utilities import extract_assertion, extract_constraints_from_patch
from synthesis import load_components, load_specification, synthesize, Program, program_to_formula, \
    collect_symbols, RuntimeSymbol, ComponentSymbol, verify, program_to_code
from pathlib import Path
from typing import List, Dict, Tuple
from main import emitter, definitions, values
from pysmt.shortcuts import is_sat, get_model, Symbol, BV, Equals, EqualsOrIff, And, Or, TRUE, FALSE, Select, BVConcat, \
    SBV

check_counter = 0


def reduce(current_patch_set: List[Dict[str, Program]], path_to_concolic_exec_result: str, concrete_input: [],
           assertion) -> List[Tuple[str, Program]]:  # TODO
    # Reduces the set of patch candidates based on the current path constraint
    # Iterate over patches and check if they still hold based on path constraint.
    updated_patch_set = []
    for patch in current_patch_set:
        if check(patch, path_to_concolic_exec_result, concrete_input, assertion):
            updated_patch_set.append(patch)
    return updated_patch_set


def check(patch: Dict[str, Program], path_to_concolic_exec_result: str, concrete_input: [], assertion):  # TODO
    # checks, e.g., for crash freedom
    path_constraint_file_path = path_to_concolic_exec_result + "/test000001.smt2"
    path_condition = extract_assertion(path_constraint_file_path)
    patch_constraint = extract_constraints_from_patch(patch)
    specification = And(path_condition, And(assertion, patch_constraint))
    result = is_sat(specification)
    return result


def check_coverage():  # TODO
    global check_counter
    if check_counter < 10:  # Only for testing purpose.
        check_counter += 1
        return False
    else:
        return True


def generate_patch_set(project_path) -> List[Dict[str, Program]]:
    emitter.sub_title("Generating Patch Pool")
    test_output_list = values.CONF_TEST_OUTPUT
    gen_comp_files = []
    os.chdir(definitions.DIRECTORY_COMPONENTS)
    for component_name in values.CONF_GENERAL_COMP_LIST:
        gen_comp_files.append(Path(component_name))
    general_components = load_components(gen_comp_files)

    proj_comp_files = []
    os.chdir(project_path)
    for component_name in values.CONF_CUSTOM_COMP_LIST:
        proj_comp_files.append(Path(component_name))
    project_components = load_components(proj_comp_files)

    components = project_components + general_components
    depth = values.DEFAULT_DEPTH
    if values.CONF_DEPTH_VALUE.isnumeric():
        depth = int(values.CONF_DEPTH_VALUE)

    spec_files = []
    for output_spec in test_output_list:
        spec_files.append((Path("t1.smt2"), Path("klee-out-" + str(test_output_list.index(output_spec)))))
    specification = load_specification(spec_files)

    concrete_enumeration = True
    lower_bound = values.DEFAULT_LOWER_BOUND
    upper_bound = values.DEFAULT_UPPER_BOUND

    result = synthesize(components, depth, specification, concrete_enumeration, lower_bound, upper_bound)

    list_of_patches = [_ for _ in result]
    emitter.normal("\tnumber of patches in pool: " + str(len(list_of_patches)))
    return list_of_patches


def print_patch_list(patch_list):
    count = 0
    emitter.sub_title("List of Synthesised Patches")
    for patch in patch_list:
        count = count + 1
        emitter.sub_sub_title("Patch #" + str(count))
        emitter.emit_patch(patch)


def run(project_path, program_name):
    emitter.title("Repairing Program")
    program_path = project_path + "/" + program_name
    ## Generate all possible solutions by running the synthesizer.
    P = generate_patch_set(project_path)
    ppc_log_path = project_path + "/klee-last/ppc.log"
    expr_log_path = project_path + "/klee-last/expr.log"

    emitter.sub_title("Evaluating Patch Pool")
    satisfied = len(P) <= 1
    iteration = 0
    assertion = values.SPECIFICATION

    while not satisfied and len(P) > 1:
        iteration = iteration + 1
        emitter.sub_sub_title("Iteration: " + str(iteration))
        ## Pick new input and patch candidate for next concolic execution step.
        argument_list = values.ARGUMENT_LIST
        second_var_list = values.SECOND_VAR_LIST
        gen_arg_list, gen_var_list, P = generate_new_input(ppc_log_path, expr_log_path, project_path, argument_list,
                                                           second_var_list, P)  # TODO (later) patch candidate missing
        if not gen_arg_list and not gen_var_list:
            emitter.warning("\t\t[warning] no more paths to generate new input")
            break
        assert gen_arg_list  # there should be a concrete input
        # print(">> new input: " + str(gen_arg_list))

        ## Concolic execution of concrete input and patch candidate to retrieve path constraint.
        exit_code = run_concolic_execution(program_path + ".bc", gen_arg_list, gen_var_list)
        assert exit_code == 0

        ## Reduces the set of patch candidates based on the current path constraint
        P = reduce(P, project_path + "/klee-last/", gen_arg_list, assertion)
        emitter.debug("|P|=", str(len(P)))

        # Checks for the current coverage.
        satisfied = check_coverage()
    print_patch_list(P)
