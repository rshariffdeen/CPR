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
from main import emitter, values, reader, parallel, definitions, extractor, oracle, utilities, generator, merger, oracle, generator
import re
import struct
import random
import copy



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
        values.LIST_PATCH_UNDERAPPROX_CHECK[patch_index] = 1
        if values.CONF_REFINE_METHOD in ["under-approx", "overfit"]:
            while not universal_quantification:
                emitter.debug("refining for universal quantification")
                model = generator.generate_model(specification)
                refined_patch_space = refine_patch_space(model, refined_patch_space, path_condition, patch_constraint)
                if refined_patch_space is None:
                    break
                constant_constraint = generator.generate_constant_constraint_formula(refined_patch_space)
                patch_space_constraint = And(patch_constraint, constant_constraint)
                path_feasibility = And(path_condition, patch_space_constraint)
                specification = And(path_feasibility, Not(p_specification))
                universal_quantification = is_unsat(specification)
    else:
        values.LIST_PATCH_UNDERAPPROX_CHECK[patch_index] = 0
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
    refined_patch_space = patch_space
    if not existential_quantification:
        values.LIST_PATCH_OVERAPPROX_CHECK[patch_index] = 1
        if values.CONF_REFINE_METHOD in ["over-approx", "overfit"]:
            while not existential_quantification:
                emitter.debug("refining for existential quantification")
                model = generator.generate_model(specification)
                refined_patch_space = refine_patch_space(model, patch_space, path_condition, patch_constraint)
                if refined_patch_space is None:
                    break
                constant_constraint = generator.generate_constant_constraint_formula(refined_patch_space)
                patch_space_constraint = And(patch_constraint, constant_constraint)
                path_feasibility = And(path_condition, patch_space_constraint)
                specification = And(path_feasibility, p_specification)
                existential_quantification = is_unsat(specification)

    else:
        values.LIST_PATCH_OVERAPPROX_CHECK[patch_index] = 0
    return refined_patch_space


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
            refined_patch_space = refine_for_over_fit(p_specification, patch_constraint, path_condition,
                                                      negated_path_condition)
            # if values.CONF_REFINE_METHOD == values.OPTIONS_REFINE_METHOD[0]:
            #     refined_patch_space = refine_for_under_approx(p_specification, patch_constraint, path_condition)
            # elif values.CONF_REFINE_METHOD == values.OPTIONS_REFINE_METHOD[1]:
            #
            #     refined_patch_space = refine_for_over_approx(p_specification, patch_constraint, negated_path_condition)
            # elif values.CONF_REFINE_METHOD == values.OPTIONS_REFINE_METHOD[2]:
            #     refined_patch_space = refine_for_over_fit(p_specification, patch_constraint, path_condition, negated_path_condition)
        else:
            values.LIST_PATCH_SCORE[patch_index] = patch_score + 1
    return refined_patch_space, index


def refine_patch_space(model, patch_space, path_condition, patch_constraint):
    refined_patch_space = dict()
    constant_list = dict()
    fixed_point_list = dict()

    for var_name in model:
        if "const_" in var_name:
            constant_list[var_name] = int(model[var_name][0])
        if "rvalue" in var_name:
            fixed_point_list[var_name] = utilities.get_signed_value(model[var_name])
    constant_count = len(constant_list)

    if constant_count == 0:
        return None

    is_multi_dimension = False
    if constant_count > 1:
        is_multi_dimension = True

    partition_list = generator.generate_partition_for_space(constant_list, patch_space, is_multi_dimension)
    refined_partition_list = refine_partition_list()

    for constant_name in constant_list:
        partition_value = constant_list[constant_name]
        constant_info = patch_space[constant_name]
        constant_info['name'] = constant_name
        constant_info['partition-value'] = partition_value
        refined_partition_list = refine_constant_range(constant_info, path_condition, patch_constraint, fixed_point_list, is_multi_dimension)
        if refined_partition_list:
            if len(refined_partition_list) == 1:
                refined_constant_range = refined_partition_list[0]
            else:
                refined_constant_range = merge_partition(refined_partition_list)
            refined_patch_space[constant_name] = refined_constant_range
        else:
            return None
    return refined_patch_space


def refine_constant_range(constant_info, path_condition, patch_constraint, fixed_point_list, is_multi_dimension):
    refined_list = list()
    constant_name = constant_info['name']
    partition_value = constant_info['partition-value']
    is_continuous = constant_info['is_continuous']
    if is_continuous:
        partition_list = generator.generate_partition_for_constant(constant_info, partition_value, is_multi_dimension)
        if not partition_list:
            return refined_list
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
            is_exist_verification = And(path_feasibility, input_fixation)
            if is_sat(is_exist_verification):
                new_model = generator.generate_model(is_exist_verification)
                new_partition_value = new_model[constant_name][0]
                constant_info['partition-value'] = new_partition_value
                child_list = refine_constant_range(constant_info, path_condition,
                                                   patch_constraint, fixed_point_list, is_multi_dimension)
                refined_list = refined_list + child_list
            else:
                emitter.data("adding space", constant_info)
                refined_list.append(copy.deepcopy(constant_info))
    else:
        if is_multi_dimension:
            constant_list = dict()
            new_constant_info = constant_info
            new_constant_info['lower-bound'] = partition_value
            new_constant_info['upper-bound'] = partition_value
            new_constant_info['is_continuous'] = True
            constant_list[constant_name] = new_constant_info
            constant_constraint = generator.generate_constant_constraint_formula(constant_list)
            patch_space_constraint = And(patch_constraint, constant_constraint)
            path_feasibility = And(path_condition, patch_space_constraint)
            input_fixation = generator.generate_input_constraint_formula(fixed_point_list)
            is_exist_verification = And(path_feasibility, input_fixation)
            if is_unsat(is_exist_verification):
                refined_list.append(copy.deepcopy(constant_info))
                return refined_list
        invalid_list = constant_info['invalid-list']
        valid_list = constant_info['valid-list']
        valid_list.remove(partition_value)
        invalid_list.append(partition_value)
        if valid_list:
            constant_info['valid-list'] = valid_list
            constant_info['invalid-list'] = invalid_list
            refined_list.append(copy.deepcopy(constant_info))

    return refined_list


def refine_partition():

    constant_constraint = generator.generate_constant_constraint_formula(constant_list)
    patch_space_constraint = And(patch_constraint, constant_constraint)
    path_feasibility = And(path_condition, patch_space_constraint)
    input_fixation = generator.generate_input_constraint_formula(fixed_point_list)
    is_exist_verification = And(path_feasibility, input_fixation)
    if is_sat(is_exist_verification):


def refine_partition_list(partition_list, constant_name_list, patch_constraint, path_condition, fixed_point_list):
    refined_list = list()
    constant_name_list = sorted(constant_name_list)
    for partition in partition_list:
        constant_list = dict()
        index = 0
        for constant_name in constant_name_list:
            lower_bound, upper_bound = partition[index]
            constant_info = dict()
            constant_info['lower-bound'] = lower_bound
            constant_info['upper-bound'] = upper_bound
            constant_list[constant_name] = constant_info
            index = index + 1
        constant_constraint = generator.generate_constant_constraint_formula(constant_list)
        patch_space_constraint = And(patch_constraint, constant_constraint)
        path_feasibility = And(path_condition, patch_space_constraint)
        input_fixation = generator.generate_input_constraint_formula(fixed_point_list)
        is_exist_verification = And(path_feasibility, input_fixation)
        if is_sat(is_exist_verification):

    constant_name = constant_info['name']
    partition_value = constant_info['partition-value']
    is_continuous = constant_info['is_continuous']
    if is_continuous:
        partition_list = generate_partition_for_constant(constant_info, partition_value, is_multi_dimension)
        if not partition_list:
            return refined_list
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
            is_exist_verification = And(path_feasibility, input_fixation)
            if is_sat(is_exist_verification):
                new_model = generator.generate_model(is_exist_verification)
                new_partition_value = new_model[constant_name][0]
                constant_info['partition-value'] = new_partition_value
                child_list = refine_constant_range(constant_info, path_condition,
                                                   patch_constraint, fixed_point_list, is_multi_dimension)
                refined_list = refined_list + child_list
            else:
                emitter.data("adding space", constant_info)
                refined_list.append(copy.deepcopy(constant_info))
    else:
        if is_multi_dimension:
            constant_list = dict()
            new_constant_info = constant_info
            new_constant_info['lower-bound'] = partition_value
            new_constant_info['upper-bound'] = partition_value
            new_constant_info['is_continuous'] = True
            constant_list[constant_name] = new_constant_info
            constant_constraint = generator.generate_constant_constraint_formula(constant_list)
            patch_space_constraint = And(patch_constraint, constant_constraint)
            path_feasibility = And(path_condition, patch_space_constraint)
            input_fixation = generator.generate_input_constraint_formula(fixed_point_list)
            is_exist_verification = And(path_feasibility, input_fixation)
            if is_unsat(is_exist_verification):
                refined_list.append(copy.deepcopy(constant_info))
                return refined_list
        invalid_list = constant_info['invalid-list']
        valid_list = constant_info['valid-list']
        valid_list.remove(partition_value)
        invalid_list.append(partition_value)
        if valid_list:
            constant_info['valid-list'] = valid_list
            constant_info['invalid-list'] = invalid_list
            refined_list.append(copy.deepcopy(constant_info))

    return refined_list
