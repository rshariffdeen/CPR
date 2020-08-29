import multiprocessing as mp
from main import emitter, oracle, definitions

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
    for control_loc in ppc_list:
        if definitions.DIRECTORY_RUNTIME in control_loc:
            continue
        ppc_list_at_loc = ppc_list[control_loc]
        for ppc in ppc_list_at_loc:
            pool.apply_async(oracle.check_path_feasibility, args=(control_loc, ppc), callback=collect_result)

    pool.close()
    emitter.normal("\t\twaiting for thread completion")
    pool.join()
    return results

