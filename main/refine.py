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


def merge_partition(partition_list, constant_name):
    merged_partition = dict()

    sorted_partition_list = sorted(partition_list, key=lambda x: x[constant_name]['lower-bound'])
    is_continuous = True
    lower_bound = None
    upper_bound = None
    invalid_list = []
    valid_list = []
    for partition in sorted_partition_list:
        p_lower_bound = partition[constant_name]['lower-bound']
        p_upper_bound = partition[constant_name]['upper-bound']
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
        invalid_list = invalid_list + list(range(values.DEFAULT_LOWER_BOUND, lower_bound)) + list(range(upper_bound + 1, values.DEFAULT_UPPER_BOUND))
        constraint_info = dict()
        constraint_info['lower-bound'] = None
        constraint_info['upper-bound'] = None
        constraint_info['valid-list'] = valid_list
        constraint_info['invalid-list'] = invalid_list
        constraint_info['is_continuous'] = False
        merged_partition[constant_name] = constraint_info
    else:
        constraint_info = dict()
        constraint_info['lower-bound'] = lower_bound
        constraint_info['upper-bound'] = upper_bound
        constraint_info['valid-list'] = []
        constraint_info['invalid-list'] = []
        constraint_info['is_continuous'] = True
        merged_partition[constant_name] = constraint_info

    return merged_partition


def refine_for_under_approx(p_specification, patch_constraint, path_condition):
    patch_constraint_str = patch_constraint.serialize()
    patch_index = utilities.get_hash(patch_constraint_str)
    patch_space = values.LIST_PATCH_CONSTRAINTS[patch_index]
    constant_constraint = generator.generate_constant_constraint_formula(patch_space)
    patch_space_constraint = And(patch_constraint, constant_constraint)
    path_feasibility = And(path_condition, patch_space_constraint)
    specification = And(path_feasibility, Not(p_specification))
    universal_quantification = is_unsat(specification)
    refined_patch_space = patch_space
    if not universal_quantification:
        emitter.debug("refining for universal quantification")
        model = generator.generate_model(specification)
        refined_patch_space = refine_patch_space(model, patch_space, path_condition, patch_constraint, Not(p_specification))
    return refined_patch_space


def refine_for_over_approx(p_specification, patch_constraint, path_condition):
    patch_constraint_str = patch_constraint.serialize()
    patch_index = utilities.get_hash(patch_constraint_str)
    patch_space = values.LIST_PATCH_CONSTRAINTS[patch_index]
    constant_constraint = generator.generate_constant_constraint_formula(patch_space)
    patch_space_constraint = And(patch_constraint, constant_constraint)
    path_feasibility = And(path_condition, patch_space_constraint)
    specification = And(path_feasibility, p_specification)
    existential_quantification = is_unsat(specification)
    if not existential_quantification:
        emitter.debug("refining for existential quantification")
        model = generator.generate_model(specification)
        refined_patch_space = refine_patch_space(model, patch_space, path_condition, patch_constraint, p_specification)
        if refined_patch_space is None:
            values.LIST_PATCH_SCORE[patch_index] = values.LIST_PATCH_SCORE[patch_index] - 10000
    return patch_space


def refine_for_over_fit(p_specification, patch_constraint, path_condition, negated_path_condition):
    patch_constraint_str = patch_constraint.serialize()
    patch_index = utilities.get_hash(patch_constraint_str)
    refined_patch_space = refine_for_under_approx(p_specification, patch_constraint, path_condition)
    values.LIST_PATCH_CONSTRAINTS[patch_index] = refined_patch_space
    if refined_patch_space is None:
        return None
    refined_patch_space = refine_for_over_approx(p_specification, patch_constraint, negated_path_condition)
    return refined_patch_space


def refine_patch(p_specification, patch_constraint, path_condition, index):
    patch_constraint_str = patch_constraint.serialize()
    patch_index = utilities.get_hash(patch_constraint_str)
    patch_space = values.LIST_PATCH_CONSTRAINTS[patch_index]
    if not patch_space:
        return None, index
    constant_constraint = generator.generate_constant_constraint_formula(patch_space)
    patch_space_constraint = And(patch_constraint, constant_constraint)
    path_feasibility = And(path_condition, patch_space_constraint)
    patch_score = values.LIST_PATCH_SCORE[patch_index]
    refined_patch_space = patch_space
    negated_path_condition = values.NEGATED_PPC_FORMULA
    if is_sat(path_feasibility):
        if oracle.is_loc_in_trace(values.CONF_LOC_BUG):
            values.LIST_PATCH_SCORE[patch_index] = patch_score + 2
            if values.CONF_REFINE_METHOD == values.OPTIONS_REFINE_METHOD[0]:
                refined_patch_space = refine_for_under_approx(p_specification, patch_constraint, path_condition)
            elif values.CONF_REFINE_METHOD == values.OPTIONS_REFINE_METHOD[1]:

                refined_patch_space = refine_for_over_approx(p_specification, patch_constraint, negated_path_condition)
            elif values.CONF_REFINE_METHOD == values.OPTIONS_REFINE_METHOD[2]:
                refined_patch_space = refine_for_over_fit(p_specification, patch_constraint, path_condition, negated_path_condition)
        else:
            values.LIST_PATCH_SCORE[patch_index] = patch_score + 1
    return refined_patch_space, index


def is_valid_range(check_range):
    lower_bound, upper_bound = check_range
    if lower_bound <= upper_bound:
        return True
    return False


def generate_partition_for_constant(constant_info, partition_value):
    partition_list = list()
    range_lower = (constant_info['lower-bound'], partition_value - 1)
    range_upper = (partition_value + 1, constant_info['upper-bound'])
    range_equal = (partition_value, partition_value)
    is_continuous = constant_info['is_continuous']
    if is_continuous:
        if is_valid_range(range_lower):
            partition_list.append(range_lower)
        if is_valid_range(range_upper):
            partition_list.append(range_upper)
    partition_list.append(range_equal)
    return partition_list

#
# def generate_new_range(constant_space, partition_list):
#     new_range_list = list()
#     constant_count = len(constant_space)
#     if constant_count == 1:
#         constant_name = list(constant_space.keys())[0]
#         constant_info = constant_space[constant_name]
#         is_continuous = constant_info['is_continuous']
#         partition_value = partition_list[constant_name]
#         if is_continuous:
#             range_lower = (constant_info['lower-bound'], partition_value - 1)
#             range_upper = (partition_value + 1, constant_info['upper-bound'])
#             if is_valid_range(range_lower):
#                 new_range_list.append((range_lower,))
#             if is_valid_range(range_upper):
#                 new_range_list.append((range_upper,))
#         else:
#             invalid_list = constant_info['invalid-list']
#             valid_list = constant_info['valid-list']
#             valid_list.remove(partition_value)
#             invalid_list.append(partition_value)
#             if valid_list:
#                 new_range_list.append((invalid_list,))
#
#     elif constant_count == 2:
#         constant_name_a = list(constant_space.keys())[0]
#         constant_name_b = list(constant_space.keys())[1]
#         constant_info_a = constant_space[constant_name_a]
#         is_continuous_a = constant_info_a['is_continuous']
#         partition_value_a = partition_list[constant_name_a]
#         constant_info_b = constant_space[constant_name_b]
#         partition_value_b = partition_list[constant_name_b]
#         is_continuous_b = constant_info_b['is_continuous']
#         if is_continuous_a:
#             range_lower_a = (constant_info_a['lower-bound'], partition_value_a - 1)
#             range_upper_a = (partition_value_a + 1, constant_info_a['upper-bound'])
#             if is_continuous_b:
#                 range_lower_b = (constant_info_b['lower-bound'], partition_value_b - 1)
#                 range_upper_b = (partition_value_b + 1, constant_info_b['upper-bound'])
#                 if is_valid_range(range_lower_a):
#                     if is_valid_range(range_lower_b):
#                         new_range_list.append((range_lower_a, range_lower_b))
#                     if is_valid_range(range_upper_b):
#                         new_range_list.append((range_lower_a, range_upper_b))
#
#                 if is_valid_range(range_upper_a):
#                     if is_valid_range(range_lower_b):
#                         new_range_list.append((range_upper_a, range_lower_b))
#                     if is_valid_range(range_upper_b):
#                         new_range_list.append((range_upper_a, range_upper_b))
#             else:
#                 invalid_list_b = constant_info_b['invalid-list']
#                 valid_list_b = constant_info_b['valid-list']
#                 valid_list_b.remove(partition_value_b)
#                 invalid_list_b.append(partition_value_b)
#                 if valid_list_b:
#                     if is_valid_range(range_lower_a):
#                         new_range_list.append((range_lower_a, invalid_list_b))
#                     if is_valid_range(range_upper_a):
#                         new_range_list.append((range_upper_a, invalid_list_b))
#
#         else:
#             if is_continuous_b:
#                 invalid_list_a = constant_info_a['invalid-list']
#                 valid_list_a = constant_info_a['valid-list']
#                 valid_list_a.remove(partition_value_a)
#                 invalid_list_a.append(partition_value_a)
#                 range_lower_b = (constant_info_b['lower-bound'], partition_value_b - 1)
#                 range_upper_b = (partition_value_b + 1, constant_info_b['upper-bound'])
#                 if valid_list_a:
#                     if is_valid_range(range_lower_b):
#                         new_range_list.append((invalid_list_a, range_lower_b))
#                     if is_valid_range(range_upper_b):
#                         new_range_list.append((invalid_list_a, range_upper_b))
#
#
#
#
#     elif constant_count == 3:
#         for constant_name_a in constant_space:
#             constant_info_a = constant_space[constant_name_a]
#             partition_value_a = partition_list[constant_name_a]
#             for constant_name_b in constant_space:
#                 constant_info_b = constant_space[constant_name_b]
#                 partition_value_b = partition_list[constant_name_b]
#                 for constant_name_c in constant_space:
#                     constant_info_c = constant_space[constant_name_c]
#                     partition_value_c = partition_list[constant_name_c]
#                     range_lower_a = (constant_info_a['lower-bound'], partition_value_a - 1)
#                     range_upper_a = (partition_value_a + 1, constant_info_a['upper-bound'])
#                     range_lower_b = (constant_info_b['lower-bound'], partition_value_b - 1)
#                     range_upper_b = (partition_value_b + 1, constant_info_b['upper-bound'])
#                     range_lower_c = (constant_info_c['lower-bound'], partition_value_c - 1)
#                     range_upper_c = (partition_value_c + 1, constant_info_c['upper-bound'])
#
#                     new_range_list.append((range_lower_a, range_lower_b, range_lower_c))
#                     new_range_list.append((range_lower_a, range_lower_b, range_upper_c))
#                     new_range_list.append((range_lower_a, range_upper_b, range_lower_c))
#                     new_range_list.append((range_lower_a, range_upper_b, range_upper_c))
#                     new_range_list.append((range_upper_a, range_lower_b, range_lower_c))
#                     new_range_list.append((range_upper_a, range_lower_b, range_upper_c))
#                     new_range_list.append((range_upper_a, range_upper_b, range_lower_c))
#                     new_range_list.append((range_upper_a, range_upper_b, range_upper_c))
#     else:
#         utilities.error_exit("unhandled constant count in generate new range")
#
#     return new_range_list


# def generate_formula_for_range(patch, constant_space, path_condition, assertion):
#     patch_constraint = extractor.extract_constraints_from_patch(patch)
#     constant_constraint = generator.generate_constant_constraint_formula(constant_space)
#     patch_constraint = And(patch_constraint, constant_constraint)
#     path_feasibility = And(path_condition, patch_constraint)
#     formula = And(path_feasibility, assertion)
#     return formula


def refine_patch_space(model, patch_space, path_condition, patch_constraint, p_specification):
    refined_patch_space = dict()
    constant_list = dict()
    fixed_point_list = dict()

    for var_name in model:
        if "const_" in var_name:
            constant_list[var_name] = int(model[var_name][0])
        if "rvalue" in var_name:
            fixed_point_list[var_name] = utilities.get_signed_value(model[var_name])

    for constant_name in constant_list:
        partition_value = constant_list[constant_name]
        constant_info = patch_space[constant_name]
        constant_info['name'] = constant_name
        constant_info['partition-value'] = partition_value
        refined_partition_list = refine_constant_range(constant_info, path_condition, patch_constraint, p_specification, fixed_point_list)
        if refined_partition_list:
            if len(refined_partition_list) == 1:
                refined_constant_range = refined_partition_list[0]
            else:
                refined_constant_range = merge_partition(refined_partition_list, constant_name)
            refined_patch_space[constant_name] = refined_constant_range
        else:
            return None
    return refined_patch_space


def refine_constant_range(constant_info, path_condition, patch_constraint, p_specification, fixed_point_list):
    refined_list = list()
    constant_name = constant_info['name']
    partition_value = constant_info['partition-value']
    partition_list = generate_partition_for_constant(constant_info, partition_value)
    constant_list = dict()
    for const_partition in partition_list:
        lower_bound, upper_bound = const_partition
        constant_info['lower-bound'] = lower_bound
        constant_info['upper-bound'] = upper_bound
        constant_list[constant_name] = constant_info
        constant_constraint = generator.generate_constant_constraint_formula(constant_list)
        patch_space_constraint = And(patch_constraint, constant_constraint)
        path_feasibility = And(path_condition, patch_space_constraint)
        input_fixation = generator.generate_input_constraint_formula(fixed_point_list)
        fixed_path_feasibility = And(path_feasibility, input_fixation)
        is_exist_verification = And(fixed_path_feasibility, p_specification)
        is_always_verification = And(fixed_path_feasibility, Not(p_specification))
        if is_sat(is_exist_verification):
            if is_sat(is_always_verification):
                new_model = generator.generate_model(And(path_feasibility, p_specification))
                new_partition_value = new_model[constant_name]
                constant_info['partition-value'] = new_partition_value
                child_list = refine_constant_range(constant_info, path_condition,
                                                   patch_constraint, p_specification, fixed_point_list)
                refined_list = refined_list + child_list
        else:
            emitter.data("adding space", constant_info)
            refined_list.append(copy.deepcopy(constant_info))
    return refined_list
