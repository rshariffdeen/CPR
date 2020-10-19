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


def refine_for_under_approx(p_specification, patch_constraint, path_condition):
    patch_constraint_str = patch_constraint.serialize()
    patch_index = utilities.get_hash(patch_constraint_str)
    constant_space = values.LIST_PATCH_CONSTRAINTS[patch_index]
    constant_constraint = generator.generate_constant_constraint_formula(constant_space)
    patch_space_constraint = And(patch_constraint, constant_constraint)
    path_feasibility = And(path_condition, patch_space_constraint)
    specification = And(path_feasibility, Not(p_specification))
    universal_quantification = is_unsat(specification)
    refined_constant_space = constant_space
    if not universal_quantification:
        while not universal_quantification:
            emitter.debug("refining for universal quantification")
            model = generator.generate_model(specification)
            refined_constant_space = refine_constant_range(constant_space, model, path_condition, patch_constraint, Not(p_specification))
            if refined_constant_space is None:
                break
            constant_constraint = generator.generate_constant_constraint_formula(refined_constant_space)
            patch_space_constraint = And(patch_constraint, constant_constraint)
            path_feasibility = And(path_condition, patch_space_constraint)
            specification = And(path_feasibility, Not(p_specification))
            universal_quantification = is_unsat(specification)
    return refined_constant_space


def refine_for_over_approx(p_specification, patch_constraint, path_condition):
    patch_constraint_str = patch_constraint.serialize()
    patch_index = utilities.get_hash(patch_constraint_str)
    constant_space = values.LIST_PATCH_CONSTRAINTS[patch_index]
    constant_constraint = generator.generate_constant_constraint_formula(constant_space)
    patch_space_constraint = And(patch_constraint, constant_constraint)
    path_condition = values.NEGATED_PPC_FORMULA
    path_feasibility = And(path_condition, patch_space_constraint)
    specification = And(path_feasibility, p_specification)
    existential_quantification = is_unsat(specification)
    refined_constant_space = constant_space
    if not existential_quantification:
        while not existential_quantification:
            emitter.debug("refining for existential quantification")
            model = generator.generate_model(specification)
            refined_constant_space = refine_constant_range(constant_space, model, path_condition, patch_constraint, p_specification)
            if refined_constant_space is None:
                break
            constant_constraint = generator.generate_constant_constraint_formula(refined_constant_space)
            patch_space_constraint = And(patch_constraint, constant_constraint)
            path_feasibility = And(path_condition, patch_space_constraint)
            specification = And(path_feasibility, p_specification)
            existential_quantification = is_unsat(specification)
    return refined_constant_space


def refine_for_over_fit(p_specification, patch_constraint, path_condition):
    patch_constraint_str = patch_constraint.serialize()
    patch_index = utilities.get_hash(patch_constraint_str)
    constant_space = values.LIST_PATCH_CONSTRAINTS[patch_index]
    constant_constraint = generator.generate_constant_constraint_formula(constant_space)
    patch_space_constraint = And(patch_constraint, constant_constraint)
    negated_path_condition = values.NEGATED_PPC_FORMULA
    path_feasibility = And(negated_path_condition, patch_space_constraint)
    specification = And(path_feasibility, p_specification)
    existential_quantification = is_unsat(specification)
    refined_constant_space = constant_space
    return refined_constant_space


def refine_patch_space(p_specification, patch_constraint, path_condition, index):
    patch_constraint_str = patch_constraint.serialize()
    patch_index = utilities.get_hash(patch_constraint_str)
    constant_space = values.LIST_PATCH_CONSTRAINTS[patch_index]
    constant_constraint = generator.generate_constant_constraint_formula(constant_space)
    patch_space_constraint = And(patch_constraint, constant_constraint)
    path_feasibility = And(path_condition, patch_space_constraint)
    patch_score = values.LIST_PATCH_SCORE[patch_index]
    refined_constant_space = constant_space
    if is_sat(path_feasibility):
        if oracle.is_loc_in_trace(values.CONF_LOC_BUG):
            values.LIST_PATCH_SCORE[patch_index] = patch_score + 2
            if values.CONF_REFINE_METHOD == values.OPTIONS_REFINE_METHOD[0]:
                refined_constant_space = refine_for_under_approx(p_specification, patch_constraint, path_condition)
            elif values.CONF_REFINE_METHOD == values.OPTIONS_REFINE_METHOD[1]:
                refined_constant_space = refine_for_over_approx(p_specification, patch_constraint, path_condition)
            elif values.CONF_REFINE_METHOD == values.OPTIONS_REFINE_METHOD[2]:
                refined_constant_space = refine_for_over_fit(p_specification, patch_constraint, path_condition)
        else:
            values.LIST_PATCH_SCORE[patch_index] = patch_score + 1
    return refined_constant_space, index


def is_valid_range(range):
    lower_bound, upper_bound = range
    if lower_bound <= upper_bound:
        return True
    return False


def generate_new_range(constant_space, partition_list):
    new_range_list = list()
    constant_count = len(constant_space)
    if constant_count == 1:
        for constant_name in constant_space:
            constant_info = constant_space[constant_name]
            partition_value = partition_list[constant_name]
            range_lower = (constant_info['lower-bound'], partition_value - 1)
            range_upper = (partition_value + 1, constant_info['upper-bound'])
            if is_valid_range(range_lower):
                new_range_list.append((range_lower,))
            if is_valid_range(range_upper):
                new_range_list.append((range_upper,))

    elif constant_count == 2:
        for constant_name_a in constant_space:
            constant_info_a = constant_space[constant_name_a]
            partition_value_a = partition_list[constant_name_a]
            for constant_name_b in constant_space:
                constant_info_b = constant_space[constant_name_b]
                partition_value_b = partition_list[constant_name_b]
                range_lower_a = (constant_info_a['lower-bound'], partition_value_a - 1)
                range_upper_a = (partition_value_a + 1, constant_info_a['upper-bound'])
                range_lower_b = (constant_info_b['lower-bound'], partition_value_b - 1)
                range_upper_b = (partition_value_b + 1, constant_info_b['upper-bound'])

                if is_valid_range(range_lower_a):
                    if is_valid_range(range_lower_b):
                        new_range_list.append((range_lower_a, range_lower_b))
                    if is_valid_range(range_upper_b):
                        new_range_list.append((range_lower_a, range_upper_b))

                if is_valid_range(range_upper_a):
                    if is_valid_range(range_lower_b):
                        new_range_list.append((range_upper_a, range_lower_b))
                    if is_valid_range(range_upper_b):
                        new_range_list.append((range_upper_a, range_upper_b))

    elif constant_count == 3:
        for constant_name_a in constant_space:
            constant_info_a = constant_space[constant_name_a]
            partition_value_a = partition_list[constant_name_a]
            for constant_name_b in constant_space:
                constant_info_b = constant_space[constant_name_b]
                partition_value_b = partition_list[constant_name_b]
                for constant_name_c in constant_space:
                    constant_info_c = constant_space[constant_name_c]
                    partition_value_c = partition_list[constant_name_c]
                    range_lower_a = (constant_info_a['lower-bound'], partition_value_a - 1)
                    range_upper_a = (partition_value_a + 1, constant_info_a['upper-bound'])
                    range_lower_b = (constant_info_b['lower-bound'], partition_value_b - 1)
                    range_upper_b = (partition_value_b + 1, constant_info_b['upper-bound'])
                    range_lower_c = (constant_info_c['lower-bound'], partition_value_c - 1)
                    range_upper_c = (partition_value_c + 1, constant_info_c['upper-bound'])

                    new_range_list.append((range_lower_a, range_lower_b, range_lower_c))
                    new_range_list.append((range_lower_a, range_lower_b, range_upper_c))
                    new_range_list.append((range_lower_a, range_upper_b, range_lower_c))
                    new_range_list.append((range_lower_a, range_upper_b, range_upper_c))
                    new_range_list.append((range_upper_a, range_lower_b, range_lower_c))
                    new_range_list.append((range_upper_a, range_lower_b, range_upper_c))
                    new_range_list.append((range_upper_a, range_upper_b, range_lower_c))
                    new_range_list.append((range_upper_a, range_upper_b, range_upper_c))
    else:
        utilities.error_exit("unhandled constant count in generate new range")

    return new_range_list


def generate_formula_for_range(patch, constant_space, path_condition, assertion):
    patch_constraint = extractor.extract_constraints_from_patch(patch)
    constant_constraint = generator.generate_constant_constraint_formula(constant_space)
    patch_constraint = And(patch_constraint, constant_constraint)
    path_feasibility = And(path_condition, patch_constraint)
    formula = And(path_feasibility, assertion)
    return formula


def refine_constant_range(constant_space, model, path_condition, patch_constraint, p_specification):
    refined_patch = None
    constant_count = len(constant_space)
    refined_constant_space = None
    partition_list = dict()

    for var_name in model:
        if "const_" in var_name:
            partition_list[var_name] = int(model[var_name][0])
        if "rvalue" in var_name:
            bit_vector = model[var_name]
            contradiction_value = utilities.get_signed_value(bit_vector)
            array = Symbol(var_name, ArrayType(BV32, BV8))
            array_value = BVConcat(Select(array, BV(3, 32)),
                 BVConcat(Select(array, BV(2, 32)),
                 BVConcat(Select(array, BV(1, 32)), Select(array, BV(0, 32)))))
            assertion = Equals(array_value, BV(contradiction_value, 32))

    range_list = generate_new_range(constant_space, partition_list)
    for partition_range in range_list:
        partitioned_constant_space = dict()
        index = 0
        for constant_name in constant_space:
            constant_info = constant_space[constant_name]
            lower_bound, upper_bound = partition_range[index]
            constant_info['lower-bound'] = lower_bound
            constant_info['upper-bound'] = upper_bound
            partitioned_constant_space[constant_name] = constant_info
            index = index + 1

        emitter.data("partitioned space", partitioned_constant_space)
        constant_constraint = generator.generate_constant_constraint_formula(partitioned_constant_space)
        patch_space_constraint = And(patch_constraint, constant_constraint)
        path_feasibility = And(path_condition, patch_space_constraint)
        is_exist_verification = And(path_feasibility, assertion)
        is_always_verification = And(path_feasibility, p_specification)
        if is_sat(is_exist_verification):
            if is_sat(is_always_verification):
                if refined_constant_space is None:
                    refined_constant_space = partitioned_constant_space
                    emitter.data("refined space", refined_constant_space)
                    return refined_constant_space
        else:
            refined_constant_space = partitioned_constant_space
            emitter.data("refined space", refined_constant_space)
            return refined_constant_space

    emitter.data("refined space", refined_constant_space)
    return refined_constant_space

