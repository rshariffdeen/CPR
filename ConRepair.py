import os
import time
from pathlib import Path
from main import emitter, logger, definitions, values, builder, repair, \
    configuration, reader, distance, synthesis, parallel
from main.utilities import extract_byte_code, error_exit
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


def load_component_list():
    emitter.normal("loading custom/general components")
    gen_comp_files = []
    os.chdir(definitions.DIRECTORY_COMPONENTS)
    if values.CONF_GENERAL_COMP_LIST:
        for component_name in values.CONF_GENERAL_COMP_LIST:
            gen_comp_files.append(Path(component_name))
    else:
        component_file_list = os.listdir(definitions.DIRECTORY_COMPONENTS)
        for comp_file in component_file_list:
            if ".smt2" in comp_file:
                gen_comp_files.append(Path(comp_file))
    general_components = synthesis.load_components(gen_comp_files)

    proj_comp_files = []
    os.chdir(values.CONF_PATH_PROJECT)
    for component_name in values.CONF_CUSTOM_COMP_LIST:
        proj_comp_files.append(Path(component_name))
    project_components = synthesis.load_components(proj_comp_files)
    values.LIST_COMPONENTS = project_components + general_components


def bootstrap(arg_list):
    emitter.title("Starting " + values.TOOL_NAME)
    emitter.sub_title("Loading Configurations")
    configuration.read_conf(arg_list)
    configuration.read_conf_file()

    binary_dir_path = "/".join(values.CONF_PATH_PROGRAM.split("/")[:-1])
    values.FILE_PPC_LOG = binary_dir_path + "/klee-last/ppc.log"
    values.FILE_EXPR_LOG = binary_dir_path + "/klee-last/expr.log"
    values.FILE_TRACE_LOG = binary_dir_path + "/klee-last/trace.log"
    definitions.DIRECTORY_OUTPUT = definitions.DIRECTORY_OUTPUT_BASE + "/" + values.CONF_TAG_ID
    if not os.path.isdir(definitions.DIRECTORY_OUTPUT):
        os.mkdir(definitions.DIRECTORY_OUTPUT)

    # set location of bug/crash
    if not values.CONF_BUG_LOCATION:
        values.CONF_BUG_LOCATION = reader.collect_crash_point(values.FILE_TRACE_LOG)

    if values.CONF_MAX_BOUND:
        values.DEFAULT_UPPER_BOUND = values.CONF_MAX_BOUND
    if values.CONF_LOW_BOUND:
        values.DEFAULT_LOWER_BOUND = values.CONF_LOW_BOUND
    if values.CONF_MAX_FORK:
        values.DEFAULT_MAX_FORK = values.DEFAULT_MAX_FORK

    load_component_list()


def initialize():
    emitter.title("Initializing Program")
    program_path = values.CONF_PATH_PROGRAM
    test_input_list = values.CONF_TEST_INPUT
    for argument_list in test_input_list:
        emitter.sub_title("Running concrete execution for test case: " + str(argument_list))
        emitter.debug("input list in test case:", argument_list)
        values.ARGUMENT_LIST = argument_list
        if "$POC" in argument_list:
            argument_list.replace("$POC", values.CONF_PATH_POC)
        extract_byte_code(program_path)
        exit_code = run_concrete_execution(program_path + ".bc", argument_list, True)
        assert exit_code == 0

        emitter.sub_title("Running concolic execution for test case: " + str(argument_list))
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
    try:
        main(sys.argv[1:])
    except KeyboardInterrupt as e:
        parallel.pool.terminate()
        error_exit("Program Interrupted by User")
