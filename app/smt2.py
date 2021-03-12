from pysmt.shortcuts import is_sat, Not, And, Or, TRUE, BVSGE, BVSLE, Int, NotEquals, SBV, Equals, BVConcat, Select, BV
from pysmt.typing import BV32, BV8, ArrayType
from pysmt.shortcuts import write_smtlib, get_model, Symbol, is_sat, is_unsat, to_smtlib


def generate_constraint_for_input_space(input_space):
    formula = None
    for input_partition in input_space:
        sub_formula = generate_constraint_for_input_partition(input_partition)
        if formula is None:
            formula = sub_formula
        else:
            formula = Or(formula, sub_formula)
    return formula


def generate_constraint_for_patch_space(patch_space):
    formula = None
    for patch_partition in patch_space:
        sub_formula = generate_constraint_for_patch_partition(patch_partition)
        if formula is None:
            formula = sub_formula
        else:
            formula = Or(formula, sub_formula)
    return formula


def generate_constraint_for_patch_partition(patch_partition):
    formula = None
    for parameter_name in patch_partition:
        sym_var = Symbol(parameter_name, BV32)
        constraint_info = patch_partition[parameter_name]
        upper_bound = int(constraint_info['upper-bound'])
        lower_bound = int(constraint_info['lower-bound'])
        sub_formula = And(BVSGE(SBV(upper_bound, 32), sym_var), BVSLE(SBV(lower_bound, 32), sym_var))
        if formula is None:
            formula = sub_formula
        else:
            formula = And(formula, sub_formula)
    return formula


def generate_constraint_for_input_partition(input_partition):
    formula = None
    for var_name in input_partition:
        sym_array = Symbol(var_name, ArrayType(BV32, BV8))
        sym_var = BVConcat(Select(sym_array, BV(3, 32)),
                           BVConcat(Select(sym_array, BV(2, 32)),
                                    BVConcat(Select(sym_array, BV(1, 32)), Select(sym_array, BV(0, 32)))))
        constant_info = input_partition[var_name]
        upper_bound = int(constant_info['upper-bound'])
        lower_bound = int(constant_info['lower-bound'])
        sub_formula = And(BVSGE(SBV(upper_bound, 32), sym_var), BVSLE(SBV(lower_bound, 32), sym_var))
        if formula is None:
            formula = sub_formula
        else:
            formula = And(formula, sub_formula)
    return formula