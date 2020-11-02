import re
from six.moves import cStringIO
from pysmt.shortcuts import And
import os

from main import emitter, utilities
from pathlib import Path
from pysmt.smtlib.parser import SmtLibParser
from main.synthesis import program_to_formula, collect_symbols, RuntimeSymbol, ComponentSymbol
from main.utilities import execute_command


def extract_var_relationship(var_expr_map):
    # preserve user-input : program variable relationship
    # include program variable names for program specification
    parser = SmtLibParser()
    relationship = None
    for expr_map in var_expr_map:
        prog_var_name, prog_var_expr = expr_map[0]
        angelic_var_name, angelic_var_expr = expr_map[1]
        prog_dependent_var_list = set(re.findall("\(select (.+?) \(_ ", prog_var_expr))
        angelic_dependent_var_list = set(re.findall("\(select (.+?) \(_ ", angelic_var_expr))
        dependent_var_list = set(list(prog_dependent_var_list) + list(angelic_dependent_var_list))

        str_script = "(set-logic QF_AUFBV )\n"
        str_script += "(declare-fun " + prog_var_name + " () (Array (_ BitVec 32) (_ BitVec 8) ) )\n"
        for var_d in dependent_var_list:
            str_script += "(declare-fun " + var_d + " () (Array (_ BitVec 32) (_ BitVec 8) ) )\n"
        str_script += "(assert (= " + prog_var_expr + " " + angelic_var_expr + " ))\n"
        str_script += "(assert (= " + prog_var_name + " " + angelic_var_name + " ))\n"
        str_script += "(exit)\n"
        script = parser.get_script(cStringIO(str_script))
        formula = script.get_last_formula()
        if not relationship:
            relationship = formula
        else:
            relationship = And(relationship, formula)
    return relationship


def extract_bit_vector(expression_str):
    bit_vector = dict()
    if "[" in expression_str:
        token_list = expression_str.split("[")
        token_list.remove(token_list[0])
        for token in token_list:
            if ".." in token:
                continue
            index_str, value_str = token.split(" := ")
            index = int(index_str.split("_")[0])
            value = int(value_str.split("_")[0])
            bit_vector[index] = value
    return bit_vector


def extract_byte_code(binary_path):
    emitter.normal("\textracting bytecode")
    directory_path = "/".join(binary_path.split("/")[:-1])
    binary_name = binary_path.split("/")[-1]
    extract_command = "cd " + directory_path + ";"
    extract_command += "extract-bc " + binary_name
    execute_command(extract_command)


def extract_assertion(spec_file_path):
    spec_dir_path = "/".join(spec_file_path.split("/")[:-1])
    spec_file_name = spec_file_path.split("/")[-1]
    current_dir = os.getcwd()
    os.chdir(spec_dir_path)
    # emitter.normal("\textracting program specification")
    smt_parser = SmtLibParser()
    assertion_formula = None
    with Path(spec_file_name).open() as f:
        script = smt_parser.get_script(f)
        assertion_formula = script.get_last_formula()
    os.chdir(current_dir)
    return assertion_formula


def extract_formula_from_patch(patch):
    lid = list(patch.keys())[0]
    eid = 0
    patch_component = patch[lid]
    patch_constraint = program_to_formula(patch_component)
    program_substitution = {}
    for program_symbol in collect_symbols(patch_constraint, lambda x: True):
        kind = ComponentSymbol.check(program_symbol)
        data = ComponentSymbol.parse(program_symbol)._replace(lid=lid)._replace(eid=eid)
        if kind == ComponentSymbol.RRETURN:
            program_substitution[program_symbol] = RuntimeSymbol.angelic(data)
        elif kind == ComponentSymbol.RVALUE:
            program_substitution[program_symbol] = RuntimeSymbol.rvalue(data)
        elif kind == ComponentSymbol.LVALUE:
            program_substitution[program_symbol] = RuntimeSymbol.lvalue(data)
        else:
            pass  # FIXME: do I need to handle it somehow?
    substituted_patch = patch_constraint.substitute(program_substitution)
    return substituted_patch


def extract_input_list(model):
    input_list = dict()
    for var_name in model:
        if "rvalue!" in str(var_name) and "_" not in str(var_name):
            byte_list = model[var_name]
            input_list[str(var_name)] = utilities.get_signed_value(byte_list)
    is_multi_dimension = False
    if len(input_list) > 1:
        is_multi_dimension = True
    return input_list, is_multi_dimension


def extract_parameter_list(model):
    parameter_list = dict()
    for var_name in model:
        if "const_" in str(var_name):
            byte_list = model[var_name]
            parameter_list[str(var_name)] = utilities.get_signed_value(byte_list)
    is_multi_dimension = False
    if len(parameter_list) > 1:
        is_multi_dimension = True
    return parameter_list, is_multi_dimension


def extract_input_arg_list(argument_str):
    if "[" not in argument_str:
        argument_list = str(argument_str).split(" ")
    else:
        argument_str = argument_str.replace("[", "").replace("]", "")
        argument_list = str(argument_str).split(",")
    return argument_list
