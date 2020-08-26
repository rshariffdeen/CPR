import os
import time
from main import emitter, logger, definitions, values, builder, repair, configuration, reader, distance
from main.utilities import extract_byte_code
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


def bootstrap(arg_list):
    emitter.title("Starting " + values.TOOL_NAME)
    emitter.sub_title("Loading Configurations")
    configuration.read_conf(arg_list)
    configuration.read_conf_file()


def initialize():
    emitter.title("Initializing Program")
    program_path = values.CONF_PATH_PROGRAM
    test_input_list = values.CONF_TEST_INPUT
    binary_dir_path = "/".join(values.CONF_PATH_PROGRAM.split("/")[:-1])
    values.FILE_PPC_LOG = binary_dir_path + "/klee-last/ppc.log"
    values.FILE_EXPR_LOG = binary_dir_path + "/klee-last/expr.log"
    values.FILE_TRACE_LOG = binary_dir_path + "/klee-last/trace.log"

    # set location of bug/crash
    if not values.CONF_BUG_LOCATION:
        values.CONF_BUG_LOCATION = reader.collect_crash_point(values.FILE_TRACE_LOG)

    if values.CONF_MAX_BOUND:
        values.DEFAULT_UPPER_BOUND = values.CONF_MAX_BOUND
    if values.CONF_LOW_BOUND:
        values.DEFAULT_LOWER_BOUND = values.CONF_LOW_BOUND
    if values.CONF_MAX_FORK:
        values.DEFAULT_MAX_FORK = values.DEFAULT_MAX_FORK


    for argument_list in test_input_list:
        emitter.sub_title("Running initial concrete execution")
        emitter.debug("input list in test case:", argument_list)
        values.ARGUMENT_LIST = argument_list
        if "$POC" in argument_list:
            argument_list.replace("$POC", values.CONF_PATH_POC)
        extract_byte_code(program_path)
        exit_code = run_concrete_execution(program_path + ".bc", argument_list, {}, True)
        assert exit_code == 0

        emitter.sub_title("Running initial concolic Execution")
        extract_byte_code(program_path)
        exit_code = run_concolic_execution(program_path + ".bc", argument_list, {}, True)
        assert exit_code == 0

        distance.update_distance_map()


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
    assert os.path.isfile(values.CONF_PATH_PROGRAM)
    assert os.path.getsize(values.CONF_PATH_PROGRAM) > 0
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
