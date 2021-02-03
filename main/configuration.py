import os
import sys
import shutil
from pathlib import Path
from main import emitter, logger, definitions, values, reader, synthesis
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
                    emitter.emit_help()
                    exit()
                values.CONF_SELECTION_STRATEGY = values.OPTIONS_SELECT_METHOD[option]
            elif definitions.ARG_OPERATION_MODE in arg:
                option = int(arg.replace(definitions.ARG_OPERATION_MODE, ''))
                if option not in values.OPTIONS_OPERATION_MODE:
                    emitter.error(
                        "Invalid option for " + definitions.ARG_OPERATION_MODE.replace("=", "") + " : " + arg)
                    emitter.emit_help()
                    exit()
                values.CONF_OPERATION_MODE = values.OPTIONS_OPERATION_MODE[option]
            elif definitions.ARG_PATCH_TYPE in arg:
                option = int(arg.replace(definitions.ARG_PATCH_TYPE, ''))
                if option not in values.OPTIONS_PATCH_TYPE:
                    emitter.error("Invalid option for " + definitions.ARG_PATCH_TYPE.replace("=", "") + " : " + arg)
                    emitter.emit_help()
                    exit()
                values.CONF_PATCH_TYPE = values.OPTIONS_PATCH_TYPE[option]
            elif definitions.ARG_REFINE_METHOD in arg:
                option = int(arg.replace(definitions.ARG_REFINE_METHOD, ''))
                if option not in values.OPTIONS_REFINE_METHOD:
                    emitter.error("Invalid option for " + definitions.ARG_REFINE_METHOD.replace("=", "") + " : " + arg)
                    emitter.emit_help()
                    exit()
                values.CONF_REFINE_METHOD = values.OPTIONS_REFINE_METHOD[option]
            elif definitions.ARG_REDUCE_METHOD in arg:
                option = int(arg.replace(definitions.ARG_REDUCE_METHOD, ''))
                if option not in values.OPTIONS_REDUCE_METHOD:
                    emitter.error("Invalid option for " + definitions.ARG_REDUCE_METHOD.replace("=", "") + " : " + arg)
                    emitter.emit_help()
                    exit()
                values.CONF_REDUCE_METHOD = values.OPTIONS_REDUCE_METHOD[option]
            elif definitions.ARG_SKIP_BUILD in arg:
                values.CONF_SKIP_BUILD = True
            elif definitions.ARG_ITERATION_COUNT in arg:
                values.CONF_ITERATION_LIMIT = int(arg.replace(definitions.ARG_ITERATION_COUNT, ""))
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
                    emitter.emit_help()
                    exit()
                else:
                    time_split = arg.replace(definitions.ARG_CEGIS_TIME_SPLIT, "")
                    values.CONF_TIME_SPLIT = time_split

            else:
                emitter.error("Invalid argument: " + arg)
                emitter.emit_help()
                exit()
    else:
        emitter.emit_help()
        exit()


def read_conf_file():
    emitter.normal("reading configuration values form configuration file")
    emitter.note("\t[file] " + values.FILE_CONFIGURATION)
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
        elif definitions.CONF_BINARY_PATH in configuration:
            values.CONF_PATH_PROGRAM = configuration.replace(definitions.CONF_BINARY_PATH, '')
        elif definitions.CONF_COMMAND_BUILD in configuration:
            values.CONF_COMMAND_BUILD = configuration.replace(definitions.CONF_COMMAND_BUILD, '')
        elif definitions.CONF_COMMAND_CONFIG in configuration:
            values.CONF_COMMAND_CONFIG = configuration.replace(definitions.CONF_COMMAND_CONFIG, '')
        elif definitions.CONF_RANK_LIMIT in configuration:
            values.CONF_RANK_LIMIT = int(configuration.replace(definitions.CONF_RANK_LIMIT, ''))
        elif definitions.CONF_TEST_FILE in configuration:
            values.CONF_TEST_FILE = configuration.replace(definitions.CONF_TEST_FILE, '')
            if not os.path.isfile(values.CONF_TEST_FILE):
                error_exit("Test file " + values.CONF_TEST_FILE + " not found")
        elif definitions.CONF_TEST_OUTPUT in configuration:
            values.CONF_TEST_OUTPUT = configuration.replace(definitions.CONF_TEST_OUTPUT, '').split(",")
        elif definitions.CONF_TEST_INPUT in configuration:
             input_list = configuration.replace(definitions.CONF_TEST_INPUT, '').split("],[")
             processed_list = []
             for input in input_list:
                 processed_list.append(input.replace("[", "").replace("]", ""))
             values.CONF_TEST_INPUT = processed_list
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
            values.CONF_DIR_SRC = configuration.replace(definitions.CONF_DIR_SRC, '').replace("//", "/")
            if values.CONF_DIR_SRC:
                if values.CONF_DIR_SRC[-1] == "/":
                    values.CONF_DIR_SRC = values.CONF_DIR_SRC[:-1]
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
        elif definitions.CONF_TIMEOUT_KLEE in configuration:
            values.CONF_TIMEOUT_KLEE = int(configuration.replace(definitions.CONF_TIMEOUT_KLEE, ''))

    if not values.CONF_TAG_ID:
        emitter.error("[NOT FOUND] Tag ID ")
        exit()
    if values.CONF_DIR_SRC:
        if "/" != values.CONF_DIR_SRC[0]:
            values.CONF_DIR_SRC = values.CONF_PATH_PROJECT + "/" + values.CONF_DIR_SRC
    else:
        values.CONF_DIR_SRC = values.CONF_PATH_PROJECT
    if "/" != values.CONF_PATH_PROGRAM[0]:
        values.CONF_PATH_PROGRAM = values.CONF_DIR_SRC + "/" + values.CONF_PATH_PROGRAM


def load_component_list():
    emitter.normal("loading custom/general components")
    base_list = ["equal.smt2", "not-equal.smt2", "less-than.smt2", "less-or-equal.smt2"]
    if definitions.DIRECTORY_TESTS in values.CONF_PATH_PROJECT:
        base_list = []
    gen_comp_files = []
    os.chdir(definitions.DIRECTORY_COMPONENTS)
    if values.CONF_GENERAL_COMP_LIST and not values.CONF_ALL_COMPS:
        comp_list = list(set(values.CONF_GENERAL_COMP_LIST + base_list))
        for component_name in comp_list:
            gen_comp_files.append(Path(component_name))
            emitter.note("\tloading component: " + str(component_name))
    else:
        component_file_list = os.listdir(definitions.DIRECTORY_COMPONENTS)
        for comp_file in component_file_list:
            if ".smt2" in comp_file:
                if any(x in comp_file for x in ["logical-not", "post-decrement", "post-increment", "minus", "constant", "assignment", "sequence", "greater", "remainder"]):
                    continue
                gen_comp_files.append(Path(comp_file))
                emitter.note("\tloading component: " + str(comp_file))
    gen_comp_files = list(set(gen_comp_files))
    general_components = synthesis.load_components(gen_comp_files)

    proj_comp_files = []
    os.chdir(values.CONF_PATH_PROJECT)
    for component_name in values.CONF_CUSTOM_COMP_LIST:
        proj_comp_files.append(Path(component_name))
        emitter.note("\tloading component: " + str(component_name))
    project_components = synthesis.load_components(proj_comp_files)
    values.LIST_COMPONENTS = project_components + general_components
    values.COUNT_COMPONENTS = len(values.LIST_COMPONENTS)
    values.COUNT_COMPONENTS_CUS = len(project_components)
    values.COUNT_COMPONENTS_GEN = len(general_components)


def print_configuration():
    # emitter.note("\tconfiguration.is_crash:" + str(values.IS_CRASH))
    # assertion_formula = generator.generate_formula(values.SPECIFICATION_TXT[1])
    # emitter.configuration("\t[config] program specification:", values.SPECIFICATION_TXT[1])
    emitter.configuration("path generation limit", values.DEFAULT_GEN_SEARCH_LIMIT)
    emitter.configuration("synthesis max bound", values.DEFAULT_PATCH_UPPER_BOUND)
    emitter.configuration("synthesis low bound", values.DEFAULT_PATCH_LOWER_BOUND)
    emitter.configuration("stack size", sys.getrecursionlimit())
    emitter.configuration("refine strategy", values.DEFAULT_REFINE_METHOD)
    emitter.configuration("patch type", values.DEFAULT_PATCH_TYPE)
    emitter.configuration("repair method", values.DEFAULT_REDUCE_METHOD)
    emitter.configuration("timeout for sat", values.DEFAULT_TIMEOUT_SAT)
    emitter.configuration("timeout for klee", values.DEFAULT_TIMEOUT_KLEE)
    emitter.configuration("distance metric", values.DEFAULT_DISTANCE_METRIC)
    emitter.configuration("operation mode", values.DEFAULT_OPERATION_MODE)
    emitter.configuration("iteration limit", values.DEFAULT_ITERATION_LIMIT)


def update_configuration():
    emitter.normal("updating configuration values")
    binary_dir_path = "/".join(values.CONF_PATH_PROGRAM.split("/")[:-1])
    values.FILE_PPC_LOG = binary_dir_path + "/klee-last/ppc.log"
    values.FILE_EXPR_LOG = binary_dir_path + "/klee-last/expr.log"
    values.FILE_TRACE_LOG = binary_dir_path + "/klee-last/trace.log"
    values.FILE_MESSAGE_LOG = binary_dir_path + "/klee-last/messages.txt"
    definitions.DIRECTORY_OUTPUT = definitions.DIRECTORY_OUTPUT_BASE + "/" + values.CONF_TAG_ID
    definitions.DIRECTORY_LOG = definitions.DIRECTORY_LOG_BASE + "/" + values.CONF_TAG_ID

    if os.path.isdir(definitions.DIRECTORY_OUTPUT):
        shutil.rmtree(definitions.DIRECTORY_OUTPUT)
    os.mkdir(definitions.DIRECTORY_OUTPUT)

    if os.path.isdir(definitions.DIRECTORY_LOG):
        shutil.rmtree(definitions.DIRECTORY_LOG)
    os.mkdir(definitions.DIRECTORY_LOG)

    if values.CONF_MAX_BOUND:
        values.DEFAULT_PATCH_UPPER_BOUND = values.CONF_MAX_BOUND
    if values.CONF_LOW_BOUND:
        values.DEFAULT_PATCH_LOWER_BOUND = values.CONF_LOW_BOUND
    if values.CONF_MAX_FORK:
        values.DEFAULT_MAX_FORK = values.CONF_MAX_FORK
    if values.CONF_GEN_SEARCH_LIMIT:
        values.DEFAULT_GEN_SEARCH_LIMIT = values.CONF_GEN_SEARCH_LIMIT
    if values.CONF_ITERATION_LIMIT >= 0:
        values.DEFAULT_ITERATION_LIMIT = values.CONF_ITERATION_LIMIT
    if values.CONF_STACK_SIZE:
        values.DEFAULT_STACK_SIZE = values.CONF_STACK_SIZE
    if values.CONF_IS_CRASH:
        values.IS_CRASH = values.CONF_IS_CRASH
    if values.CONF_TIME_DURATION:
        values.DEFAULT_TIME_DURATION = values.CONF_TIME_DURATION
    if values.CONF_TIMEOUT_SAT:
        values.DEFAULT_TIMEOUT_SAT = values.CONF_TIMEOUT_SAT
    if values.CONF_TIMEOUT_KLEE:
        values.DEFAULT_TIMEOUT_KLEE = values.CONF_TIMEOUT_KLEE
    if values.CONF_RANK_LIMIT:
        values.DEFAULT_PATCH_RANK_LIMIT = values.CONF_RANK_LIMIT
    if values.CONF_SELECTION_STRATEGY:
        values.DEFAULT_SELECTION_STRATEGY = values.CONF_SELECTION_STRATEGY
    if values.CONF_DISTANCE_METRIC:
        values.DEFAULT_DISTANCE_METRIC = values.CONF_DISTANCE_METRIC
    if values.CONF_PATCH_TYPE:
        values.DEFAULT_PATCH_TYPE = values.CONF_PATCH_TYPE
    if values.CONF_REFINE_METHOD:
        values.DEFAULT_REFINE_METHOD = values.CONF_REFINE_METHOD
    if values.CONF_OPERATION_MODE:
        values.DEFAULT_OPERATION_MODE = values.CONF_OPERATION_MODE
    if values.CONF_REDUCE_METHOD:
        values.DEFAULT_REDUCE_METHOD = values.CONF_REDUCE_METHOD

    if values.CONF_TIME_SPLIT:
        explore, refine = values.CONF_TIME_SPLIT.split(":")
        total = int(explore) + int(refine)
        values.CONF_TIME_CEGIS_EXPLORE = (int(explore) / total) * values.DEFAULT_TIME_DURATION
        values.CONF_TIME_CEGIS_REFINE = (int(refine) / total) * values.DEFAULT_TIME_DURATION

    sys.setrecursionlimit(values.DEFAULT_STACK_SIZE)
