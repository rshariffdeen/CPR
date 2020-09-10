from main import definitions, values, emitter
from pysmt.shortcuts import is_sat, Not, And
from pysmt.smtlib.parser import SmtLibParser
from six.moves import cStringIO
from main.reader import collect_symbolic_expression
from main.synthesis import Program
from typing import Dict


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


def check_path_feasibility(chosen_control_loc, ppc, lock):
    """
    This function will check if a selected path is feasible
           ppc : partial path conditoin at chosen control loc
           chosen_control_loc: branch location selected for flip
           returns satisfiability of the negated path
    """
    parser = SmtLibParser()
    script = parser.get_script(cStringIO(ppc))
    formula = script.get_last_formula()
    prefix = formula.arg(0)
    # prefix_constraint_list = list()
    # while prefix.is_and():
    #     if prefix == values.PREFIX_PPC_FORMULA:
    #         break
    #     if str(prefix.arg(1).serialize()) not in values.LIST_KLEE_ASSUMPTIONS:
    #         prefix_constraint_list.append(prefix.arg(1))
    #     prefix = prefix.arg(0)
    #
    # prefix = None
    # if prefix_constraint_list:
    #     prefix = prefix_constraint_list[0]
    #     for p in prefix_constraint_list[1:]:
    #         prefix = And(prefix, p)
    #
    constraint = formula.arg(1)
    # if definitions.DIRECTORY_RUNTIME in chosen_control_loc:
    #     values.LIST_KLEE_ASSUMPTIONS.append(str(constraint.serialize()))
    new_path = And(prefix, Not(constraint))
    # print(control_loc, constraint)
    assert str(new_path.serialize()) != str(formula.serialize())
    if is_sat(new_path):
        return True, chosen_control_loc, new_path
    else:
        #with lock:
        emitter.debug("Path is not satisfiable at " + str(chosen_control_loc), new_path)
        return False, chosen_control_loc, new_path


def check_patch_feasibility(assertion, var_relationship, patch_constraint, path_condition, index):  # TODO
    specification = And(path_condition, patch_constraint)
    if assertion:
        if values.IS_CRASH:
            if is_loc_in_trace(values.CONF_LOC_BUG):
                exist_valid_instance = is_sat(And(specification, And(assertion, var_relationship)))
                exist_invalid_instance = is_sat(And(specification, And(Not(assertion), var_relationship)))
                result = exist_valid_instance and not exist_invalid_instance
            else:
                result = is_sat(specification)
        else:
            exist_valid_instance = is_sat(And(specification, And(assertion, var_relationship)))
            exist_invalid_instance = is_sat(And(specification, And(Not(assertion), var_relationship)))
            result = exist_valid_instance and not exist_invalid_instance
    else:
        if values.IS_CRASH:
            if is_loc_in_trace(values.CONF_LOC_BUG):
                result = False
            else:
                result = is_sat(specification)
        else:
            result = is_sat(specification)

    return result, index
