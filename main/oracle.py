from main import definitions, values, emitter, utilities, extractor
from pysmt.shortcuts import is_sat, Not, And, is_unsat
from pysmt.smtlib.parser import SmtLibParser
from six.moves import cStringIO


import sys
if not sys.warnoptions:
    import warnings
    warnings.simplefilter("ignore")


def did_program_crash(program_output):
    if any(crash_word in str(program_output).lower() for crash_word in definitions.crash_word_list):
        return True
    return False


def any_runtime_error(program_output):
    if any(error_word in str(program_output).lower() for error_word in definitions.error_word_list):
        return True
    return False


def is_loc_on_stack(source_path, function_name, line_number, stack_info):
    # print(source_path, function_name, line_number)
    if source_path in stack_info.keys():
        # print(source_path)
        source_info = stack_info[source_path]
        if function_name in source_info.keys():
            # print(function_name)
            line_list = source_info[function_name]
            # print(line_list)
            if str(line_number) in line_list:
                # print(line_number)
                return True
    return False


def is_loc_on_sanitizer(source_path, line_number, suspicious_lines):
    # print(source_path, line_number)
    # print(suspicious_lines)
    source_loc = source_path + ":" + str(line_number)
    if source_loc in suspicious_lines.keys():
        return True
    return False


def is_loc_in_trace(source_loc):
    return source_loc in values.LIST_TRACE


def check_path_feasibility(chosen_control_loc, new_path, index):
    """
    This function will check if a selected path is feasible
           ppc : partial path conditoin at chosen control loc
           chosen_control_loc: branch location selected for flip
           returns satisfiability of the negated path
    """
    result = False
    if chosen_control_loc != values.CONF_LOC_PATCH:
        result = not is_unsat(new_path)
    else:
        result = is_sat(new_path)

    if result:
        return True, index
    else:
        emitter.data("Path is not satisfiable at " + str(chosen_control_loc), new_path)
        return False, index


def check_patch_feasibility(assertion, var_relationship, patch_constraint, path_condition, index):  # TODO
    path_constraint = And(path_condition, patch_constraint)
    patch_score = 0
    is_under_approx = None
    is_over_approx = None
    result = True
    if assertion:
        if is_sat(path_constraint):
            if is_loc_in_trace(values.CONF_LOC_BUG):
                patch_score = 2
                is_under_approx = not is_unsat(And(path_constraint, Not(assertion)))
                if values.CONF_REFINE_METHOD in ["under-approx", "overfit"]:
                    if is_under_approx:
                        emitter.debug("removing due to universal quantification")
                        result = False

                negated_path_condition = values.NEGATED_PPC_FORMULA
                path_constraint = And(negated_path_condition, patch_constraint)
                is_over_approx = not is_unsat(And(path_constraint, assertion))
                if values.CONF_REFINE_METHOD in ["over-approx", "overfit"]:
                    if is_over_approx:
                        emitter.debug("removing due to existential quantification")
                        result = False
            else:
                patch_score = 1
            # else:
            #     specification = And(path_condition, Not(patch_constraint))
            #     existential_quantification = is_unsat(And(specification, assertion))
            #     result = existential_quantification

    return result, index, patch_score, is_under_approx, is_over_approx


def check_input_feasibility(index, patch_constraint, new_path):
    check_sat = And(new_path, patch_constraint)
    result = not is_unsat(check_sat)
    return result, index


def is_valid_range(check_range):
    lower_bound, upper_bound = check_range
    if lower_bound <= upper_bound:
        return True
    return False


def is_component_constant(patch_comp):
    (cid, semantics), children = patch_comp
    if "constant" in cid:
        return True
    return False


def is_same_children(patch_comp):
    (_, _), children = patch_comp
    right_child = children['right']
    left_child = children['left']
    (cid_right, _), _ = right_child
    (cid_left, _), _ = left_child
    if cid_left == cid_right:
        return True
    return False


def is_tree_redundant(tree):
    (cid, semantics), children = tree
    if len(children) == 2:
        right_child = children['right']
        left_child = children['left']
        if cid in ["less-than", "less-or-equal", "greater-than", "greater-or-equal", "equal", "not-equal"]:
            is_right_constant = is_component_constant(right_child)
            is_left_constant = is_component_constant(left_child)
            if is_right_constant and is_left_constant:
                return True
            if is_same_children(tree):
                return True

        if cid in ["logical-or", "logical-and"]:
            is_right_redundant = is_tree_redundant(right_child)
            is_left_redundant = is_tree_redundant(left_child)
            if is_right_redundant or is_left_redundant:
                return True
    return False


def is_patch_redundant(patch, index):
    program = patch[list(patch.keys())[0]]
    tree, _ = program
    result = is_tree_redundant(tree)
    return result, index
