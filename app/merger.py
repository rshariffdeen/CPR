from pysmt.shortcuts import is_sat, Not, And, TRUE
from pysmt.shortcuts import is_unsat
from app import utilities, smt2


def get_sorted_space(partition_list):
    dimension_list = list(partition_list[0].keys())
    dim_count = len(dimension_list)
    merged_space = None
    if dim_count == 1:
        merged_space = sorted(partition_list, key=lambda x: x[dimension_list[0]]['lower-bound'])
    elif dim_count == 2:
        merged_space = sorted(partition_list, key=lambda x: (x[dimension_list[0]]['lower-bound'],
                                                             x[dimension_list[1]]['lower-bound']))
    elif dim_count == 3:
        merged_space = sorted(partition_list, key=lambda x: (x[dimension_list[0]]['lower-bound'],
                                                             x[dimension_list[1]]['lower-bound'],
                                                             x[dimension_list[2]]['lower-bound']))
    elif dim_count == 4:
        merged_space = sorted(partition_list, key=lambda x: (x[dimension_list[0]]['lower-bound'],
                                                             x[dimension_list[1]]['lower-bound'],
                                                             x[dimension_list[2]]['lower-bound'],
                                                             x[dimension_list[3]]['lower-bound']))
    else:
        utilities.error_exit("unhandled sorting of multi-dimensional space")
    return merged_space


def merge_space(partition_list, path_condition, specification):
    merged_space = get_sorted_space(partition_list)
    len_partition = len(merged_space)
    partition_id = 0
    count_iteration = 0
    if len_partition == 1:
        return partition_list
    while len_partition > 1:
        partition_a = merged_space[partition_id % len_partition]
        if not partition_a:
            merged_space.remove(partition_a)
            continue
        partition_b = merged_space[(partition_id + 1) % len_partition]
        merged_partition = merge_two_partitions(partition_a, partition_b)
        if merged_partition:
            dimension_list = list(merged_partition.keys())
            dimension_name = dimension_list[0]
            if "const_" in dimension_name:
                partition_constraints = smt2.generate_constraint_for_patch_partition(merged_partition)
            else:
                partition_constraints = smt2.generate_constraint_for_input_partition(merged_partition)
            if is_unsat(And(partition_constraints, And(path_condition, Not(specification)))):
                insert_index = merged_space.index(partition_a)
                merged_space.remove(partition_a)
                merged_space.remove(partition_b)
                merged_space.insert(insert_index, merged_partition)
                len_partition = len(merged_space)
                count_iteration = 0
        partition_id = (partition_id + 1) % len_partition
        if count_iteration == len_partition:
            break
        count_iteration = count_iteration + 1
    return merged_space


def merge_two_partitions(partition_a, partition_b):
    dimension_list = list(partition_a.keys())
    merged_partition = dict()
    for dimension_name in dimension_list:
        dimension_a = partition_a[dimension_name]['lower-bound'], partition_a[dimension_name]['upper-bound']
        dimension_b = partition_b[dimension_name]['lower-bound'], partition_b[dimension_name]['upper-bound']
        merged_dimension = merge_two_dimensions(dimension_a, dimension_b)
        if merged_dimension is None:
            return None
        merged_partition[dimension_name] = dict()
        merged_partition[dimension_name]['lower-bound'] = merged_dimension[0]
        merged_partition[dimension_name]['upper-bound'] = merged_dimension[1]
    return merged_partition


def merge_two_dimensions(range_a, range_b):
    lb_a, ub_a = range_a
    lb_b, ub_b = range_b

    if range_a == range_b:
        return range_a

    if lb_a <= lb_b and ub_b <= ub_a:
        return range_a

    if lb_b <= lb_a and ub_a <= ub_b:
        return range_b

    if lb_a == ub_b + 1:
        return lb_b, ub_a

    if lb_b == ub_a + 1:
        return lb_a, ub_b

    if lb_b == ub_a or lb_a == ub_b:
        lb = lb_a
        if lb_b <= lb_a:
            lb = lb_b
        ub = ub_b
        if ub_b <= ub_a:
            ub = ub_a
        return lb, ub

    # TODO: do I need to handle intermediate intersections?

    return None
