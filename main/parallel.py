import multiprocessing as mp
pool = mp.Pool(mp.cpu_count())

results = []


def collect_result(result):
    global results
    results.append(result)


def compute_path_feasibility(compute_fun, constraint_list, chosen_control_loc):
    chosen_constraint_list_at_loc = constraint_list[chosen_control_loc]
    for constraint in enumerate(constraint_list):
        pool.apply_async(compute_fun, args=(constraint_list, chosen_control_loc, constraint), callback=collect_result)
    pool.close()
    pool.join()
    return results
