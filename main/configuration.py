import os
from main import emitter, definitions, values, reader, logger
from main.utilities import error_exit


def read_conf(arg_list):
    emitter.normal("reading configuration values from arguments")
    if len(arg_list) > 0:
        for arg in arg_list:
            if definitions.ARG_DEBUG in arg:
                values.DEBUG = True
            elif definitions.ARG_CONF_FILE in arg:
                values.FILE_CONFIGURATION = str(arg).replace(definitions.ARG_CONF_FILE, '')
            elif definitions.ARG_DISABLE_DISTANCE_CAL in arg:
                values.IS_DISABLE_DISTANCE_CAL = True
            elif definitions.ARG_DIST_METRIC in arg:
                option = int(arg.replace(definitions.ARG_DIST_METRIC, ''))
                values.CONF_DISTANCE_METRIC = values.OPTIONS_DIST_METRIC[option]
            elif definitions.ARG_RANK_LIMIT in arg:
                values.CONF_RANK_LIMIT = int(arg.replace(definitions.ARG_RANK_LIMIT, ""))
            elif definitions.ARG_SELECTION_METHOD in arg:
                option = int(arg.replace(definitions.ARG_SELECTION_METHOD, ''))
                if option not in values.OPTIONS_SELECT_METHOD:
                    emitter.error("Invalid option for " + definitions.ARG_SELECTION_METHOD.replace("=", "") + " : " + arg)
                    emitter.help()
                    exit()
                values.CONF_SELECTION_STRATEGY = values.OPTIONS_SELECT_METHOD[option]
            elif definitions.ARG_OPERATION_MODE in arg:
                option = int(arg.replace(definitions.ARG_OPERATION_MODE, ''))
                if option not in values.OPTIONS_OPERATION_MODE:
                    emitter.error(
                        "Invalid option for " + definitions.ARG_OPERATION_MODE.replace("=", "") + " : " + arg)
                    emitter.help()
                    exit()
                values.CONF_OPERATION_MODE = values.OPTIONS_OPERATION_MODE[option]
            elif definitions.ARG_PATCH_TYPE in arg:
                option = int(arg.replace(definitions.ARG_PATCH_TYPE, ''))
                if option not in values.OPTIONS_PATCH_TYPE:
                    emitter.error("Invalid option for " + definitions.ARG_PATCH_TYPE.replace("=", "") + " : " + arg)
                    emitter.help()
                    exit()
                values.CONF_PATCH_TYPE = values.OPTIONS_PATCH_TYPE[option]
            elif definitions.ARG_REFINE_METHOD in arg:
                option = int(arg.replace(definitions.ARG_REFINE_METHOD, ''))
                if option not in values.OPTIONS_REFINE_METHOD:
                    emitter.error("Invalid option for " + definitions.ARG_REFINE_METHOD.replace("=", "") + " : " + arg)
                    emitter.help()
                    exit()
                values.CONF_REFINE_METHOD = values.OPTIONS_REFINE_METHOD[option]
            elif definitions.ARG_REDUCE_METHOD in arg:
                option = int(arg.replace(definitions.ARG_REDUCE_METHOD, ''))
                if option not in values.OPTIONS_REDUCE_METHOD:
                    emitter.error("Invalid option for " + definitions.ARG_REDUCE_METHOD.replace("=", "") + " : " + arg)
                    emitter.help()
                    exit()
                values.CONF_REDUCE_METHOD = values.OPTIONS_REDUCE_METHOD[option]
            elif definitions.ARG_SKIP_BUILD in arg:
                values.CONF_SKIP_BUILD = True
            elif definitions.ARG_COMP_ALL in arg:
                values.CONF_ALL_COMPS = True
            elif definitions.ARG_SKIP_GENERATION in arg:
                values.CONF_SKIP_GEN = True
            elif definitions.ARG_SKIP_TEST in arg:
                values.CONF_SKIP_TEST = True
            elif definitions.ARG_TIME_DURATION in arg:
                values.CONF_TIME_DURATION = int(arg.replace(definitions.ARG_TIME_DURATION, ""))
            elif definitions.ARG_CEGIS_TIME_SPLIT in arg:
                if ":" not in arg:
                    emitter.error("Invalid option for " + definitions.ARG_CEGIS_TIME_SPLIT.replace("=", "") + " : " + arg)
                    emitter.help()
                    exit()
                else:
                    time_split = arg.replace(definitions.ARG_CEGIS_TIME_SPLIT, "")
                    values.CONF_TIME_SPLIT = time_split

            else:
                emitter.error("Invalid argument: " + arg)
                emitter.help()
                exit()
    else:
        emitter.help()
        exit()


def read_conf_file():
    emitter.normal("reading configuration values form configuration file")
    logger.information(values.FILE_CONFIGURATION)
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
            values.CONF_TEST_INPUT = configuration.replace(definitions.CONF_TEST_INPUT, '').split("],[")
        elif definitions.CONF_PATH_SPECIFICATION in configuration:
            values.CONF_PATH_SPECIFICATION = configuration.replace(definitions.CONF_PATH_SPECIFICATION, '')
            assertion_file_path = values.CONF_PATH_PROJECT + "/" + values.CONF_PATH_SPECIFICATION
            values.SPECIFICATION_TXT = reader.collect_specification(assertion_file_path)
        elif definitions.CONF_CUSTOM_COMP_LIST in configuration:
            values.CONF_CUSTOM_COMP_LIST = configuration.replace(definitions.CONF_CUSTOM_COMP_LIST, '').split(",")
        elif definitions.CONF_GENERAL_COMP_LIST in configuration:
            values.CONF_GENERAL_COMP_LIST = configuration.replace(definitions.CONF_GENERAL_COMP_LIST, '').split(",")
        elif definitions.CONF_DEPTH_VALUE in configuration:
            values.CONF_DEPTH_VALUE = configuration.replace(definitions.CONF_DEPTH_VALUE, '')
        elif definitions.CONF_DIR_SRC in configuration:
            values.CONF_DIR_SRC = configuration.replace(definitions.CONF_DIR_SRC, '')
        elif definitions.CONF_LOC_BUG in configuration:
            values.CONF_LOC_BUG = configuration.replace(definitions.CONF_LOC_BUG, '')
        elif definitions.CONF_LOC_PATCH in configuration:
            values.CONF_LOC_PATCH = configuration.replace(definitions.CONF_LOC_PATCH, '')
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
        elif definitions.CONF_GEN_SEARCH_LIMIT in configuration:
            values.CONF_GEN_SEARCH_LIMIT = int(configuration.replace(definitions.CONF_GEN_SEARCH_LIMIT, ''))
        elif definitions.CONF_TAG_ID in configuration:
            values.CONF_TAG_ID = configuration.replace(definitions.CONF_TAG_ID, '')
        elif definitions.CONF_STATIC in configuration:
            conf_text = configuration.replace(definitions.CONF_STATIC, '')
            if "true" in str(conf_text).lower():
                values.CONF_STATIC = True
        elif definitions.CONF_IS_CRASH in configuration:
            conf_text = configuration.replace(definitions.CONF_IS_CRASH, '')
            if "true" in str(conf_text).lower():
                values.CONF_IS_CRASH = True
        elif definitions.CONF_IS_CPP in configuration:
            conf_text = configuration.replace(definitions.CONF_IS_CPP, '')
            if "true" in str(conf_text).lower():
                values.CONF_IS_CPP = True
        elif definitions.CONF_FLAG_ASAN in configuration:
            values.CONF_FLAG_ASAN = configuration.replace(definitions.CONF_FLAG_ASAN, '')
        elif definitions.CONF_FLAGS_C in configuration:
            values.CONF_FLAGS_C = configuration.replace(definitions.CONF_FLAGS_C, '')
        elif definitions.CONF_FLAGS_CXX in configuration:
            values.CONF_FLAGS_CXX = configuration.replace(definitions.CONF_FLAGS_CXX, '')
        elif definitions.CONF_SELECTION_STRATEGY in configuration:
            values.CONF_SELECTION_STRATEGY = configuration.replace(definitions.CONF_SELECTION_STRATEGY, '')
            if values.CONF_SELECTION_STRATEGY not in values.OPTIONS_SELECT_METHOD:
                error_exit("Invalid configuration for " + definitions.CONF_SELECTION_STRATEGY)
        elif definitions.CONF_DISTANCE_METRIC in configuration:
            values.CONF_DISTANCE_METRIC = configuration.replace(definitions.CONF_DISTANCE_METRIC, '')
            if values.CONF_DISTANCE_METRIC not in values.OPTIONS_DIST_METRIC.values():
                error_exit("Invalid configuration for " + definitions.CONF_DISTANCE_METRIC)
        elif definitions.CONF_PATCH_TYPE in configuration:
            values.CONF_PATCH_TYPE = configuration.replace(definitions.CONF_PATCH_TYPE, '')
            if values.CONF_PATCH_TYPE not in values.OPTIONS_PATCH_TYPE:
                error_exit("Invalid configuration for " + definitions.CONF_PATCH_TYPE)
        elif definitions.CONF_OPERATION_MODE in configuration:
            values.CONF_OPERATION_MODE = configuration.replace(definitions.CONF_OPERATION_MODE, '')
            if values.CONF_OPERATION_MODE not in values.OPTIONS_OPERATION_MODE:
                error_exit("Invalid configuration for " + definitions.CONF_OPERATION_MODE)
        elif definitions.CONF_BUILD_FLAGS in configuration:
            values.CONF_BUILD_FLAGS = configuration.replace(definitions.CONF_BUILD_FLAGS, '')
        elif definitions.CONF_KLEE_FLAGS in configuration:
            values.CONF_KLEE_FLAGS = configuration.replace(definitions.CONF_KLEE_FLAGS, '')
        elif definitions.CONF_ITERATION_LIMIT in configuration:
            values.CONF_ITERATION_LIMIT = int(configuration.replace(definitions.CONF_ITERATION_LIMIT, ''))
        elif definitions.CONF_STACK_SIZE in configuration:
            values.CONF_STACK_SIZE = int(configuration.replace(definitions.CONF_STACK_SIZE, ''))
        elif definitions.CONF_MASK_ARG in configuration:
            values.CONF_MASK_ARG = configuration.replace(definitions.CONF_MASK_ARG, '').split(",")
        elif definitions.CONF_TIMEOUT_SAT in configuration:
            values.CONF_TIMEOUT_SAT = int(configuration.replace(definitions.CONF_TIMEOUT_SAT, ''))

    if not values.CONF_TAG_ID:
        emitter.error("[NOT FOUND] Tag ID ")
        exit()
    values.CONF_DIR_SRC = values.CONF_PATH_PROJECT + "/" + values.CONF_DIR_SRC
    values.CONF_PATH_PROGRAM = values.CONF_DIR_SRC + "/" + values.CONF_PATH_PROGRAM
