import multiprocessing as mp
from main import emitter, oracle, definitions, extractor, refine, values, generator, concolic, utilities, distance
from typing import List, Dict, Optional
from main.synthesis import Component, enumerate_trees, Specification, Program, extract_lids, extract_assigned, verify_parallel, ComponentSymbol
from pysmt.shortcuts import is_sat, Not, And, TRUE


pool = mp.Pool(mp.cpu_count())
result_list = []


def collect_result(result):
    global result_list
    result_list.append(result)


def collect_patch(patch):
    global result_list
    result, program = patch
    if result:
        for (lid, x) in program.items():
            tree, constant = x
            if constant:
                result_list.append({lid: (tree, constant)})
            else:
                result_list.append({lid: (tree, {ComponentSymbol.parse(f).name: v for (f, v) in result.constants.items()})})


def generate_symbolic_paths_parallel(ppc_list):
    global pool, result_list
    result_list = []
    path_list = []
    filtered_list = []
    lock = None
    count = 0
    ppc_list.reverse()
    if values.CONF_OPERATION_MODE in ["sequential", "semi-parallel"]:
        for control_loc, ppc in ppc_list:
            if definitions.DIRECTORY_LIB in control_loc:
                continue
            count = count + 1
            if count == values.DEFAULT_GEN_SEARCH_LIMIT:
                break
            new_path = generator.generate_flipped_path(ppc)
            new_path_str = new_path.serialize()
            ppc_len = len(str(new_path.serialize()))
            path_list.append((control_loc, new_path, ppc_len))
            if new_path_str not in values.LIST_PATH_CHECK:
                values.LIST_PATH_CHECK.append(new_path_str)
                result_list.append(oracle.check_path_feasibility(control_loc, new_path, count - 1))

    else:
        emitter.normal("\t\tstarting parallel computing")
        pool = mp.Pool(mp.cpu_count())
        for control_loc, ppc in ppc_list:
            if definitions.DIRECTORY_LIB in control_loc:
                continue
            count = count + 1
            if count == values.DEFAULT_GEN_SEARCH_LIMIT:
                break
            new_path = generator.generate_flipped_path(ppc)
            new_path_str = new_path.serialize()
            ppc_len = len(str(new_path.serialize()))
            path_list.append((control_loc, new_path, ppc_len))
            if new_path_str not in values.LIST_PATH_CHECK:
                values.LIST_PATH_CHECK.append(new_path_str)
                pool.apply_async(oracle.check_path_feasibility, args=(control_loc, new_path, count - 1), callback=collect_result)

        pool.close()
        emitter.normal("\t\twaiting for thread completion")
        pool.join()
    # assert(len(result_list) == len(path_list))
    for result in result_list:
        is_feasible, index = result
        if is_feasible:
            filtered_list.append(path_list[index])
    return filtered_list


def validate_patches_parallel(patch_list, path_condition, assertion):
    global pool, result_list
    result_list = []


    # test_specification = values.TEST_SPECIFICATION
    # sym_expr_map = reader.collect_symbolic_expression(expr_log_path)
    # var_relationship = extractor.extract_var_relationship(sym_expr_map)
    var_relationship = TRUE
    if values.CONF_OPERATION_MODE in ["sequential"]:
        for patch in patch_list:
            patch_constraint = extractor.extract_constraints_from_patch(patch)
            index = list(patch_list).index(patch)
            result_list.append(oracle.check_patch_feasibility(assertion, var_relationship, patch_constraint, path_condition, index))
    else:
        emitter.normal("\t\tstarting parallel computing")
        pool = mp.Pool(mp.cpu_count())
        lock = None
        for patch in patch_list:
            patch_constraint = extractor.extract_constraints_from_patch(patch)
            index = list(patch_list).index(patch)
            pool.apply_async(oracle.check_patch_feasibility, args=(assertion, var_relationship, patch_constraint, path_condition, index), callback=collect_result)
        pool.close()
        emitter.normal("\t\twaiting for thread completion")
        pool.join()
    return result_list


def refine_patch_space(patch_list, path_condition, assertion):
    global pool, result_list
    result_list = []

    if values.CONF_OPERATION_MODE in ["sequential"]:
        for patch in patch_list:
            index = list(patch_list).index(patch)
            patch_constraint = extractor.extract_constraints_from_patch(patch)
            # emitter.emit_patch(patch, message="\trefining abstract patch: ")
            result_list.append(refine.refine_patch(assertion, patch_constraint, path_condition, index))
    else:
        emitter.normal("\t\tstarting parallel computing")
        pool = mp.Pool(mp.cpu_count())
        for patch in patch_list:
            index = list(patch_list).index(patch)
            patch_constraint = extractor.extract_constraints_from_patch(patch)
            # emitter.emit_patch(patch, message="\trefining abstract patch: ")
            pool.apply_async(refine.refine_patch, args=(assertion, patch_constraint, path_condition, index), callback=collect_result)
        pool.close()
        emitter.normal("\t\twaiting for thread completion")
        pool.join()
    return result_list


def partition_input_space(path_condition, assertion):
    global pool, result_list
    result_list = []

    specification = And(path_condition, Not(assertion))
    input_space = generator.generate_input_space(path_condition)
    if oracle.is_loc_in_trace(values.CONF_LOC_BUG):
        if is_sat(specification):
            partition_model = generator.generate_model(specification)
            partition_model, is_multi_dimension = extractor.extract_input_list(partition_model)
            partition_list = generator.generate_partition_for_input_space(partition_model, input_space, is_multi_dimension)
            if values.CONF_OPERATION_MODE in ["sequential"]:
                for partition in partition_list:
                    # emitter.emit_patch(patch, message="\trefining abstract patch: ")
                    result_list.append(refine.refine_input_partition(specification, partition, is_multi_dimension))
            else:
                emitter.normal("\t\tstarting parallel computing")
                pool = mp.Pool(mp.cpu_count())
                for partition in partition_list:
                    pool.apply_async(refine.refine_input_partition, args=(specification, partition, is_multi_dimension),
                                     callback=collect_result)
                pool.close()
                emitter.normal("\t\twaiting for thread completion")
                pool.join()
        else:
            result_list.append((True, input_space))
    return result_list


def validate_input_generation(patch_list, new_path):
    global pool, result_list
    result_list = []
    if values.CONF_OPERATION_MODE in ["sequential"]:
        for patch in patch_list:
            patch_constraint = extractor.extract_constraints_from_patch(patch)
            index = list(patch_list).index(patch)
            result_list.append(oracle.check_input_feasibility(index, patch_constraint, new_path))
    else:
        emitter.normal("\t\tstarting parallel computing")
        pool = mp.Pool(mp.cpu_count())
        lock = None
        for patch in patch_list:
            patch_constraint = extractor.extract_constraints_from_patch(patch)
            index = list(patch_list).index(patch)
            pool.apply_async(oracle.check_input_feasibility, args=(index, patch_constraint, new_path), callback=collect_result)
        pool.close()
        emitter.normal("\t\twaiting for thread completion")
        pool.join()
    return result_list


def generate_patch_pool(components: List[Component],
               depth: int,
               specification: Specification,
               # Optional arguments for concrete patch enumeration
               concrete_enumeration = False,
               lower_bound = -10,
               upper_bound = +10) -> Optional[Dict[str, Program]]:
    lids = {}
    for (tid, (paths, _)) in specification.items():
        for path in paths:
            lids.update(extract_lids(path))

    assert len(lids) == 1
    (lid, typ) = list(lids.items())[0]

    global pool, result_list
    emitter.normal("\t\tstarting parallel computing")
    result_list = []
    pool = mp.Pool(mp.cpu_count())

    for tree in enumerate_trees(components, depth, typ, False, True):
        assigned = extract_assigned(tree)
        if len(assigned) != len(set(assigned)):
            continue
        if concrete_enumeration:
            for value_a in range(lower_bound, upper_bound):
                # result = verify_parallel({lid: (tree, {"a": value_a})}, specification)
                # collect_patch(result)
                pool.apply_async(verify_parallel,
                                 args=({lid: (tree, {"a": value_a})}, specification),
                                 callback=collect_patch)
        else:
            pool.apply_async(verify_parallel,
                             args=({lid: (tree, {})}, specification),
                             callback=collect_patch)

    pool.close()
    emitter.normal("\t\twaiting for thread completion")
    pool.join()
    return result_list


# def concolic_exploration_parallel():
#     global pool, result_list
#     result_list = []
#     if values.CONF_OPERATION_MODE in ["sequential"]:
#         for patch in patch_list:
#             patch_constraint = extractor.extract_constraints_from_patch(patch)
#             index = list(patch_list).index(patch)
#             result_list.append(oracle.check_input_feasibility(index, patch_constraint, new_path))
#     else:
#         emitter.normal("\t\tstarting parallel computing")
#         pool = mp.Pool(mp.cpu_count())
#         lock = None
#         for patch in patch_list:
#             patch_constraint = extractor.extract_constraints_from_patch(patch)
#             index = list(patch_list).index(patch)
#             pool.apply_async(oracle.check_input_feasibility, args=(index, patch_constraint, new_path), callback=collect_result)
#         pool.close()
#         emitter.normal("\t\twaiting for thread completion")
#         pool.join()
#     return result_list

