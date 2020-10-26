from main.synthesis import load_specification, synthesize_parallel, Program
from pathlib import Path
from typing import List, Dict, Tuple
from six.moves import cStringIO
from pysmt.shortcuts import is_sat, Not, And, TRUE
import os
from pysmt.smtlib.parser import SmtLibParser
from pysmt.typing import BV32, BV8, ArrayType
from pysmt.shortcuts import write_smtlib, get_model, Symbol, is_sat, is_unsat, Equals, Int, BVConcat, Select, BV
from main.utilities import execute_command
from main import emitter, values, reader, parallel, definitions, extractor, oracle, utilities, generator
import re
import struct
import random
import copy


def merge_space(partition_list):
    merged_space = partition_list
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
            merged_space.remove(partition_a)
            merged_space.remove(partition_b)
            merged_space.append(merged_partition)
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
