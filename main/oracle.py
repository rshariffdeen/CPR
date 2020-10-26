from main import definitions, values, emitter, utilities
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
    specification = And(path_condition, patch_constraint)
    patch_constraint_str = patch_constraint.serialize()
    patch_index = utilities.get_hash(patch_constraint_str)
    patch_score = values.LIST_PATCH_SCORE[patch_index]
    result = True
    if assertion:
        if is_sat(specification):
            if is_loc_in_trace(values.CONF_LOC_BUG):
                values.LIST_PATCH_SCORE[patch_index] = patch_score + 2
                universal_quantification = is_unsat(And(specification, Not(assertion)))
                if universal_quantification:
                    negated_path_condition = values.NEGATED_PPC_FORMULA
                    specification = And(negated_path_condition, patch_constraint)
                    existential_quantification = is_unsat(And(specification, assertion))
                    result = existential_quantification
                else:
                    result = False
            else:
                values.LIST_PATCH_SCORE[patch_index] = patch_score + 1
            # else:
            #     specification = And(path_condition, Not(patch_constraint))
            #     existential_quantification = is_unsat(And(specification, assertion))
            #     result = existential_quantification

    return result, index


def check_input_feasibility(index, patch_constraint, new_path):
    check_sat = And(new_path, patch_constraint)
    result = not is_unsat(check_sat)
    return result, index


def is_valid_range(check_range):
    lower_bound, upper_bound = check_range
    if lower_bound <= upper_bound:
        return True
    return False
