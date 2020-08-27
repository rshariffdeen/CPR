import os
from main import emitter, definitions, values
from main.utilities import error_exit, extract_assertion


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
        elif definitions.CONF_LOC_BUG in configuration:
            values.CONF_BUG_LOCATION = configuration.replace(definitions.CONF_LOC_BUG, '')
        elif definitions.CONF_PATH_POC in configuration:
            values.CONF_PATH_POC = configuration.replace(definitions.CONF_PATH_POC, '')
            if not os.path.isfile(values.CONF_PATH_POC):
                poc_path = values.CONF_PATH_PROJECT + "/" + values.CONF_PATH_POC
                if os.path.isfile(poc_path):
                    values.CONF_PATH_POC = poc_path
                else:
                    error_exit("Test file " + values.CONF_PATH_POC + " not found")
        elif definitions.CONF_LOW_BOUND in configuration:
            values.CONF_LOW_BOUND = int(configuration.replace(definitions.CONF_LOW_BOUND, ''))
        elif definitions.CONF_MAX_BOUND in configuration:
            values.CONF_MAX_BOUND = int(configuration.replace(definitions.CONF_MAX_BOUND, ''))
        elif definitions.CONF_MAX_FORK in configuration:
            values.CONF_MAX_FORK = int(configuration.replace(definitions.CONF_MAX_FORK, ''))
        elif definitions.CONF_TAG_ID in configuration:
            values.CONF_TAG_ID = configuration.replace(definitions.CONF_TAG_ID, '')

    if not values.CONF_TAG_ID:
        emitter.error("[NOT FOUND] Tag ID ")
        exit()
    values.CONF_DIR_SRC = values.CONF_PATH_PROJECT + "/" + values.CONF_DIR_SRC
    values.CONF_PATH_PROGRAM = values.CONF_DIR_SRC + "/" + values.CONF_PATH_PROGRAM
