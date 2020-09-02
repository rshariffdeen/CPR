import multiprocessing as mp
from main import emitter, oracle, definitions, extractor, reader

pool = mp.Pool(mp.cpu_count())
results = []


def collect_result(result):
    global results
    results.append(result)


def generate_symbolic_paths_parallel(ppc_list):
    global pool, results
    emitter.normal("\t\tstarting parallel computing")
    results = []
    pool = mp.Pool(mp.cpu_count())
    lock = None
    for control_loc in ppc_list:
        if definitions.DIRECTORY_RUNTIME in control_loc:
            continue
        ppc_list_at_loc = ppc_list[control_loc]
        for ppc in ppc_list_at_loc:
            pool.apply_async(oracle.check_path_feasibility, args=(control_loc, ppc, lock), callback=collect_result)

    pool.close()
    emitter.normal("\t\twaiting for thread completion")
    pool.join()
    return results


def validate_patches_parallel(patch_list, path_to_concolic_exec_result, assertion):
    global pool, results
    emitter.normal("\t\tstarting parallel computing")
    results = []
    pool = mp.Pool(mp.cpu_count())
    lock = None
    path_constraint_file_path = str(path_to_concolic_exec_result) + "/test000001.smt2"
    expr_log_path = str(path_to_concolic_exec_result) + "/expr.log"
    path_condition = extractor.extract_assertion(path_constraint_file_path)

    # test_specification = values.TEST_SPECIFICATION
    sym_expr_map = reader.collect_symbolic_expression(expr_log_path)
    var_relationship = extractor.extract_var_relationship(sym_expr_map)

    for patch in patch_list:
        patch_constraint = extractor.extract_constraints_from_patch(patch)
        index = list(patch_list).index(patch)
        pool.apply_async(oracle.check_patch_feasibility, args=(assertion, var_relationship, patch_constraint, path_condition, index), callback=collect_result)

    pool.close()
    emitter.normal("\t\twaiting for thread completion")
    pool.join()
    return results
