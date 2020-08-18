import subprocess
import os
import sys
from main import logger, emitter, values, definitions
from pathlib import Path
from pysmt.smtlib.parser import SmtLibParser
from main.synthesis import load_components, load_specification, synthesize, Program, program_to_formula, collect_symbols, RuntimeSymbol, ComponentSymbol


def execute_command(command, show_output=True):
    # Print executed command and execute it in console
    emitter.command(command)
    command = "{ " + command + " ;} 2> " + definitions.FILE_ERROR_LOG
    if not show_output:
        command += " > /dev/null"
    # print(command)
    process = subprocess.Popen([command], stdout=subprocess.PIPE, shell=True)
    (output, error) = process.communicate()
    # out is the output of the command, and err is the exit value
    return int(process.returncode)


def error_exit(*args):
    print("\n")
    for i in args:
        logger.error(i)
        emitter.error(i)
    raise Exception("Error. Exiting...")


def clean_files():
    # Remove other residual files stored in ./output/
    logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    emitter.information("Removing other residual files...")
    if os.path.isdir("output"):
        clean_command = "rm -rf " + definitions.DIRECTORY_OUTPUT
        execute_command(clean_command)


def backup_file(file_path, backup_name):
    logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    backup_command = "cp " + file_path + " " + definitions.DIRECTORY_BACKUP + "/" + backup_name
    execute_command(backup_command)


def restore_file(file_path, backup_name):
    logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    restore_command = "cp " + definitions.DIRECTORY_BACKUP + "/" + backup_name + " " + file_path
    execute_command(restore_command)


def reset_git(source_directory):
    logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    reset_command = "cd " + source_directory + ";git reset --hard HEAD"
    execute_command(reset_command)


def build_clean(program_path):
    clean_command = "cd " + program_path + "; make clean; rm -rf klee-*"
    process = subprocess.Popen([clean_command], stderr=subprocess.PIPE, shell=True)
    (output, error) = process.communicate()
    assert int(process.returncode) == 0
    return int(process.returncode)


def build_program(program_path):
    program_name = program_path.split("/")[-1]
    if os.path.isfile(program_path):
        build_clean(program_path)
    program_loc = "/".join(program_path.split("/")[:-1])
    compile_command = "cd " + program_loc + ";"
    compile_command += "export TRIDENT_CC=/concolic-repair/main/trident-cc;" \
                      "CC=\"$TRIDENT_CC\" make -e;" \
                      "extract-bc " + program_name
    process = subprocess.Popen([compile_command], stderr=subprocess.PIPE, shell=True)
    (output, error) = process.communicate()
    return int(process.returncode)


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


def extract_constraints_from_patch(patch):
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