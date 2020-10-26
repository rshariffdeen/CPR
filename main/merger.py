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


def merge_partition(partition_list):
    merged_partition = dict()
    sorted_partition_list = sorted(partition_list, key=lambda x: x['lower-bound'])
    is_continuous = True
    lower_bound = None
    upper_bound = None
    invalid_list = []
    valid_list = []
    for partition in sorted_partition_list:
        p_lower_bound = partition['lower-bound']
        p_upper_bound = partition['upper-bound']
        if lower_bound is None:
            lower_bound = p_lower_bound
            upper_bound = p_upper_bound
        else:
            if upper_bound + 1 == p_lower_bound:
                upper_bound = p_upper_bound
            else:
                is_continuous = False
                invalid_list = invalid_list + list(range(upper_bound + 1, p_lower_bound))
                upper_bound = p_upper_bound
        valid_list = valid_list + list(range(p_lower_bound, p_upper_bound + 1))

    if not is_continuous:
        invalid_list = invalid_list + list(range(values.DEFAULT_PATCH_LOWER_BOUND, lower_bound)) + list(range(upper_bound + 1, values.DEFAULT_PATCH_UPPER_BOUND + 1))
        merged_partition['lower-bound'] = None
        merged_partition['upper-bound'] = None
        merged_partition['valid-list'] = valid_list
        merged_partition['invalid-list'] = invalid_list
        merged_partition['is_continuous'] = False
    else:
        merged_partition['lower-bound'] = lower_bound
        merged_partition['upper-bound'] = upper_bound
        merged_partition['valid-list'] = []
        merged_partition['invalid-list'] = []
        merged_partition['is_continuous'] = True

    return merged_partition

