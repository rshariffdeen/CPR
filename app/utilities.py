import subprocess
import os
import sys
import signal
import random
from contextlib import contextmanager
from app import logger, emitter, values, definitions
import base64
import hashlib
import time
from app.synthesis import program_to_formula, collect_symbols, ComponentSymbol, RuntimeSymbol


def generate_formula_from_patch(patch):
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


def execute_command(command, show_output=True):
    # Print executed command and execute it in console
    command = command.encode().decode('ascii', 'ignore')
    emitter.command(command)
    command = "{ " + command + " ;} 2> " + definitions.FILE_ERROR_LOG
    if not show_output:
        command += " > /dev/null"
    # print(command)
    process = subprocess.Popen([command], stdout=subprocess.PIPE, shell=True)
    (output, error) = process.communicate()
    # out is the output of the command, and err is the exit value
    return int(process.returncode)


def error_exit(*arg_list):
    emitter.error("Repair Failed")
    for arg in arg_list:
        emitter.error(str(arg))
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
    compile_command += "export CPR_CC=/concolic-repair/app/cpr-cc;" \
                      "CC=\"$CPR_CC\" CXX=\"$CPR_CXX\" make -e;" \
                      "extract-bc " + program_name
    process = subprocess.Popen([compile_command], stderr=subprocess.PIPE, shell=True)
    (output, error) = process.communicate()
    return int(process.returncode)


@contextmanager
def timeout(time):
    signal.signal(signal.SIGALRM, raise_timeout)
    signal.alarm(time)

    try:
        yield
    except TimeoutError:
        pass
    finally:
        signal.signal(signal.SIGALRM, signal.SIG_IGN)


def raise_timeout(signum, frame):
    raise TimeoutError


def get_signed_value(bit_vector):
    """
      This function will generate the signed value for a given bit list
             bit_vector : list of bits
    """
    signed_value = 0
    for i in sorted(bit_vector.keys()):
        if i == 0:
            signed_value = int(bit_vector[i])
        else:
            signed_value += ((2 << 7) << (int(i) - 1)) * int(bit_vector[i])
    return signed_value


def get_str_value(bit_vector):
    """
      This function will generate the string value for a given bit list
             bit_vector : list of bits
    """
    str_value = ""
    char_list = dict()
    # print(bit_vector)
    for i in bit_vector:
        if int(bit_vector[i]) not in range(32, 127):
            char_list[i] = chr(random.randint(33, 122))
        else:
            char_list[i] = chr(bit_vector[i])
    # print(char_list)
    for i in sorted(char_list):
        char = char_list[i]
        str_value += char
    return str_value


def get_byte_string(bit_vector):
    """
      This function will generate the byte string for a given bit list
             bit_vector : list of bits
    """
    str_value = ""
    char_list = dict()
    # print(bit_vector)
    for i in bit_vector:
        char_list[i] = chr(bit_vector[i])
    # print(char_list)
    for i in sorted(char_list, reverse=True):
        char = char_list[i]
        str_value += char
    return str_value


def get_hash(str_value):
    str_encoded = str(str_value).encode('utf-8')
    str_hasher = hashlib.sha1(str_encoded)
    hash_value = base64.urlsafe_b64encode(str_hasher.digest()[:10])
    return hash_value


def check_budget(time_budget):  # TODO implement time budget
    if values.DEFAULT_ITERATION_LIMIT >= 0:
        if values.ITERATION_NO < values.DEFAULT_ITERATION_LIMIT:  # Only for testing purpose.
            return False
        else:
            return True
    else:
        if values.CONF_TIME_CHECK is None:
            values.CONF_TIME_CHECK = time.time()
            return False
        else:
            time_start = values.CONF_TIME_CHECK
            duration = float(format((time.time() - time_start) / 60, '.3f'))
            if int(duration) > int(time_budget):
                values.CONF_TIME_CHECK = None
                return True
        return False


def count_concrete_patches_per_template(abstract_patch):
    if values.DEFAULT_PATCH_TYPE == values.OPTIONS_PATCH_TYPE[0]:
        return 1
    patch_formula = generate_formula_from_patch(abstract_patch)
    patch_formula_str = patch_formula.serialize()
    patch_index = get_hash(patch_formula_str)
    patch_space = values.LIST_PATCH_SPACE[patch_index]
    total_concrete_count = 0

    if patch_space:
        for partition in patch_space:
            partition_concrete_count = 1
            for parameter_name in partition:
                constraint_info = partition[parameter_name]
                lower_bound = str(constraint_info['lower-bound'])
                upper_bound = str(constraint_info['upper-bound'])
                parameter_dimension = len(range(int(lower_bound), int(upper_bound) + 1))
                partition_concrete_count = partition_concrete_count * parameter_dimension
            total_concrete_count = total_concrete_count + partition_concrete_count
    return total_concrete_count


def count_concrete_patches(patch_list):
    patch_count = 0
    for abstract_patch in patch_list:
        concrete_count = count_concrete_patches_per_template(abstract_patch)
        patch_count = patch_count + concrete_count
    return patch_count
