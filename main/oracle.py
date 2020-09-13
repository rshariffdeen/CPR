from main import definitions, values, emitter
from pysmt.shortcuts import is_sat, Not, And
from pysmt.smtlib.parser import SmtLibParser
from six.moves import cStringIO
from main.reader import collect_symbolic_expression
from main.synthesis import Program, Component, Specification, extract_lids, ComponentSymbol, Formula, VerificationSuccess, program_to_formula, collect_symbols, extract_eids
from typing import List, Dict, Tuple, Set, Union, Optional, NamedTuple


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
        ppc_len = len(str(new_path.serialize()))
        return True, chosen_control_loc, new_path, ppc_len
    else:
        #with lock:
        emitter.debug("Path is not satisfiable at " + str(chosen_control_loc), new_path)
        return False, chosen_control_loc, new_path, 0


def check_patch_feasibility(assertion, var_relationship, patch_constraint, path_condition, index):  # TODO
    specification = And(path_condition, patch_constraint)
    if assertion:
        if values.IS_CRASH:
            if is_loc_in_trace(values.CONF_LOC_BUG):
                exist_valid_instance = is_sat(And(specification, assertion))
                universal_quantification = is_sat(Not(And(specification, assertion)))
                result = exist_valid_instance and universal_quantification
            else:
                result = is_sat(specification)
        else:
            exist_valid_instance = is_sat(And(specification, assertion))
            exist_invalid_instance = is_sat(And(specification, Not(assertion)))
            result = exist_valid_instance and not exist_invalid_instance
    else:
        if values.IS_CRASH:
            if is_loc_in_trace(values.CONF_LOC_BUG):
                result = not is_sat(specification)
            else:
                result = is_sat(specification)
        else:
            result = is_sat(specification)

    return result, index


def check_input_feasibility(index, patch_constraint, new_path):
    check_sat = And(new_path, patch_constraint)
    result = is_sat(check_sat)
    return result, index


# def verify_patch(programs: Union[Dict[str, Program], Dict[str, Formula]],
#            specification: Specification) -> Optional[VerificationSuccess]:
#     """Check if programs satisfy specification
#     """
#     vc = TRUE()
#
#     program_semantics = { lid:(program if isinstance(program, Formula) else program_to_formula(program))
#                           for (lid, program) in programs.items() }
#     free_variables = [v for p in program_semantics.values() for v in collect_symbols(p, ComponentSymbol.is_const)]
#
#     for tid in specification.keys():
#         test_vc = FALSE()
#
#         (paths, assertion) = specification[tid]
#
#         for path in paths:
#             lids = extract_lids(path).keys()
#
#             assert len(lids) == 1
#             lid = list(lids)[0]
#             eids = extract_eids(path, lid)
#
#             assert eids == set(range(len(eids)))
#             path_vc = path
#
#             program = program_semantics[lid]
#
#             for eid in eids:
#                 program_substitution = {}
#                 for program_symbol in collect_symbols(program, lambda x: True):
#                     kind = ComponentSymbol.check(program_symbol)
#                     data = ComponentSymbol.parse(program_symbol)._replace(lid=lid)._replace(eid=eid)
#                     if kind == ComponentSymbol.RRETURN:
#                         program_substitution[program_symbol] = RuntimeSymbol.angelic(data)
#                     elif kind == ComponentSymbol.RVALUE:
#                         program_substitution[program_symbol] = RuntimeSymbol.rvalue(data)
#                     elif kind == ComponentSymbol.LVALUE:
#                         program_substitution[program_symbol] = RuntimeSymbol.lvalue(data)
#                     else:
#                         pass #FIXME: do I need to handle it somehow?
#                 bound_program = program.substitute(program_substitution)
#                 is_branch = any_fn(ComponentSymbol.is_rbranch, ComponentSymbol.is_lbranch)
#                 exe_inst_program = Instance.of_formula(bound_program, eid, Instance.EXECUTION, is_branch)
#                 path_vc = And(path_vc, exe_inst_program)
#
#             test_vc = Or(test_vc, path_vc)
#
#         assertion_substitution = {}
#         for assertion_symbol in collect_symbols(assertion, lambda x: True):
#             symbol_data = parse_assertion_symbol(assertion_symbol)
#             assertion_substitution[assertion_symbol] = RuntimeSymbol.output(symbol_data)
#         bound_assertion = assertion.substitute(assertion_substitution)
#         test_vc = And(test_vc, bound_assertion)
#         is_special_nonconst = any_fn(RuntimeSymbol.is_special, all_fn(ComponentSymbol.is_special, complement(ComponentSymbol.is_const)))
#         instantiated_test_vc = Instance.of_formula(test_vc, tid, Instance.TEST, is_special_nonconst)
#
#         vc = And(vc, instantiated_test_vc)
#
#         # print(get_model(vc))
#         # dump(vc, "vc.smt2")
#
#     model = get_model(vc)
#     if model is None:
#         return None
#     else:
#         return VerificationSuccess({v:model[v].bv_signed_value() for v in free_variables})

