import multiprocessing as mp
from main import emitter

pool = mp.Pool(mp.cpu_count())
results = []


def collect_result(result):
    global results
    results.append(result)


def generate_symbolic_paths_parallel(ppc_list, compute_func):
    emitter.normal("\t\tstarting parallel computing")
    for control_loc in ppc_list:
        ppc_list_at_loc = ppc_list[control_loc]
        for ppc in ppc_list_at_loc:
            pool.apply_async(compute_func, args=(control_loc, ppc), callback=collect_result)

    pool.close()
    emitter.normal("\t\twaiting for thread completion")
    pool.join()
    return results

