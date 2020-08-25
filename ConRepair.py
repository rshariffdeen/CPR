import os
import time
from main import emitter, logger, definitions, values, builder, repair
from main.utilities import error_exit, extract_byte_code, extract_assertion
from main.concolic import run_concrete_execution, run_concolic_execution


def create_directories():
    if not os.path.isdir(definitions.DIRECTORY_LOG):
        os.makedirs(definitions.DIRECTORY_LOG)

    if not os.path.isdir(definitions.DIRECTORY_OUTPUT_BASE):
        os.makedirs(definitions.DIRECTORY_OUTPUT_BASE)

    if not os.path.isdir(definitions.DIRECTORY_BACKUP):
        os.makedirs(definitions.DIRECTORY_BACKUP)

    if not os.path.isdir(definitions.DIRECTORY_TMP):
        os.makedirs(definitions.DIRECTORY_TMP)


def read_conf(arg_list):
    emitter.normal("reading configuration values from arguments")
    if len(arg_list) > 0:
        for arg in arg_list:
            if definitions.ARG_DEBUG in arg:
                values.DEBUG = True
            elif definitions.ARG_CONF_FILE in arg:
                values.FILE_CONFIGURATION = str(arg).replace(definitions.ARG_CONF_FILE, '')
            else:
                emitter.error("Invalid argument: " + arg)
                emitter.help()
                exit()
    else:
        emitter.help()
        exit()


def read_conf_file():
    emitter.normal("reading configuration values form configuration file")
    if not os.path.exists(values.FILE_CONFIGURATION):
        emitter.error("[NOT FOUND] Configuration file " + values.FILE_CONFIGURATION)
        exit()
    if os.path.getsize(values.FILE_CONFIGURATION) == 0:
        emitter.error("[EMPTY] Configuration file " + values.FILE_CONFIGURATION)
        exit()
    with open(values.FILE_CONFIGURATION, 'r') as conf_file:
        configuration_list = [i.strip() for i in conf_file.readlines()]

    for configuration in configuration_list:
        if definitions.CONF_PATH_PROJECT in configuration:
            values.CONF_PATH_PROJECT = configuration.replace(definitions.CONF_PATH_PROJECT, '')
        elif definitions.CONF_NAME_PROGRAM in configuration:
            values.CONF_PATH_PROGRAM = configuration.replace(definitions.CONF_NAME_PROGRAM, '')
        elif definitions.CONF_COMMAND_BUILD in configuration:
            values.CONF_COMMAND_BUILD = configuration.replace(definitions.CONF_COMMAND_BUILD, '')
        elif definitions.CONF_COMMAND_CONFIG in configuration:
            values.CONF_COMMAND_CONFIG = configuration.replace(definitions.CONF_COMMAND_CONFIG, '')
        elif definitions.CONF_TEST_FILE in configuration:
            values.CONF_TEST_FILE = configuration.replace(definitions.CONF_TEST_FILE, '')
            if not os.path.isfile(values.CONF_TEST_FILE):
                error_exit("Test file " + values.CONF_TEST_FILE + " not found")
        elif definitions.CONF_TEST_OUTPUT in configuration:
            values.CONF_TEST_OUTPUT = configuration.replace(definitions.CONF_TEST_OUTPUT, '').split(",")
        elif definitions.CONF_TEST_INPUT in configuration:
            values.CONF_TEST_INPUT = configuration.replace(definitions.CONF_TEST_INPUT, '').split(",")
        elif definitions.CONF_PATH_SPECIFICATION in configuration:
            values.CONF_PATH_SPECIFICATION = configuration.replace(definitions.CONF_PATH_SPECIFICATION, '')
            assertion_file_path = values.CONF_PATH_PROJECT + "/" + values.CONF_PATH_SPECIFICATION
            values.SPECIFICATION = extract_assertion(assertion_file_path)
        elif definitions.CONF_CUSTOM_COMP_LIST in configuration:
            values.CONF_CUSTOM_COMP_LIST = configuration.replace(definitions.CONF_CUSTOM_COMP_LIST, '').split(",")
        elif definitions.CONF_GENERAL_COMP_LIST in configuration:
            values.CONF_GENERAL_COMP_LIST = configuration.replace(definitions.CONF_GENERAL_COMP_LIST, '').split(",")
        elif definitions.CONF_DEPTH_VALUE in configuration:
            values.CONF_DEPTH_VALUE = configuration.replace(definitions.CONF_DEPTH_VALUE, '')
        elif definitions.CONF_DIR_SRC in configuration:
            values.CONF_DIR_SRC = configuration.replace(definitions.CONF_DIR_SRC, '')


def bootstrap(arg_list):
    emitter.title("Starting " + values.TOOL_NAME)
    emitter.sub_title("Loading Configurations")
    read_conf(arg_list)
    read_conf_file()


def initialize():
    emitter.title("Initializing Program")
    values.CONF_PATH_PROGRAM = values.CONF_PATH_PROJECT + "/" + values.CONF_PATH_PROGRAM
    values.CONF_DIR_SRC = values.CONF_PATH_PROJECT + "/" + values.CONF_DIR_SRC
    program_path = values.CONF_PATH_PROGRAM
    test_input_list = values.CONF_TEST_INPUT

    for argument_list in test_input_list:
        emitter.sub_title("Running initial concrete execution")
        emitter.debug("input list in test case:", argument_list)
        values.ARGUMENT_LIST = argument_list
        extract_byte_code(program_path)
        exit_code = run_concrete_execution(program_path + ".bc", argument_list, {}, True)
        assert exit_code == 0

        emitter.sub_title("Running initial concolic Execution")
        extract_byte_code(program_path)
        exit_code = run_concolic_execution(program_path + ".bc", argument_list, {}, True)
        assert exit_code == 0


def main(arg_list):
    create_directories()
    emitter.start()
    start_time = time.time()
    time_info = dict()
    time_check = time.time()
    bootstrap(arg_list)
    time_info[definitions.KEY_DURATION_BOOTSTRAP] = str(time.time() - time_check)

    time_check = time.time()
    builder.build_normal()
    assert os.path.isfile(values.CONF_PATH_PROJECT + "/" + values.CONF_PATH_PROGRAM)
    assert os.path.getsize(values.CONF_PATH_PROJECT + "/" + values.CONF_PATH_PROGRAM) > 0
    time_info[definitions.KEY_DURATION_BUILD] = str(time.time() - time_check)

    time_check = time.time()
    initialize()
    time_info[definitions.KEY_DURATION_INITIALIZATION] = str(time.time() - time_check)

    time_check = time.time()
    repair.run(values.CONF_PATH_PROJECT, values.CONF_PATH_PROGRAM)
    time_info[definitions.KEY_DURATION_REPAIR] = str(time.time() - time_check)

    # Final running time and exit message
    time_info[definitions.KEY_DURATION_TOTAL] = str(time.time() - start_time)
    emitter.end(time_info)
    logger.end(time_info)


if __name__ == "__main__":
    import sys
    main(sys.argv[1:])
