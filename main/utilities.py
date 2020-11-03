import subprocess
import os
import sys
import signal
import random
from contextlib import contextmanager
from main import logger, emitter, values, definitions
import base64
import hashlib
import time


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
                      "CC=\"$TRIDENT_CC\" CXX=\"$TRIDENT_CXX\" make -e;" \
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
    if values.CONF_TIME_CHECK is None:
        values.CONF_TIME_CHECK = time.time()
        return False
    else:
        time_start = values.CONF_TIME_CHECK
        duration = float(format((time.time() - time_start) / 60, '.3f'))
        if int(duration) > int(time_budget):
            values.CONF_TIME_CHECK = None
            return False
    return True

    # if values.ITERATION_NO < values.DEFAULT_ITERATION_LIMIT:  # Only for testing purpose.
    #     return False
    # else:
    #     return True
