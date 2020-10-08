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

