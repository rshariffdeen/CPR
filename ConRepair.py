import os
import time
from pathlib import Path
from main import emitter, logger, definitions, values, builder, repair, \
    configuration, reader, distance, synthesis, parallel, extractor, generator
from main.utilities import error_exit
from main.concolic import run_concrete_execution, run_concolic_execution

time_info = dict()
time_check = ""
start_time = ""


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
    if values.CONF_GENERAL_COMP_LIST and not values.CONF_ALL_COMPS:
        for component_name in values.CONF_GENERAL_COMP_LIST:
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
    general_components = synthesis.load_components(gen_comp_files)

    proj_comp_files = []
    os.chdir(values.CONF_PATH_PROJECT)
    for component_name in values.CONF_CUSTOM_COMP_LIST:
        proj_comp_files.append(Path(component_name))
        emitter.note("\tloading component: " + str(component_name))
    project_components = synthesis.load_components(proj_comp_files)
    values.LIST_COMPONENTS = project_components + general_components
    values.COUNT_COMPONENTS = len(values.LIST_COMPONENTS)


def bootstrap(arg_list):
    emitter.title("Starting " + values.TOOL_NAME)
    emitter.sub_title("Loading Configurations")

    configuration.read_conf(arg_list)
    configuration.read_conf_file()

    binary_dir_path = "/".join(values.CONF_PATH_PROGRAM.split("/")[:-1])
    values.FILE_PPC_LOG = binary_dir_path + "/klee-last/ppc.log"
    values.FILE_EXPR_LOG = binary_dir_path + "/klee-last/expr.log"
    values.FILE_TRACE_LOG = binary_dir_path + "/klee-last/trace.log"
    values.FILE_MESSAGE_LOG = binary_dir_path + "/klee-last/messages.txt"
    definitions.DIRECTORY_OUTPUT = definitions.DIRECTORY_OUTPUT_BASE + "/" + values.CONF_TAG_ID
    if not os.path.isdir(definitions.DIRECTORY_OUTPUT):
        os.mkdir(definitions.DIRECTORY_OUTPUT)

    if values.CONF_MAX_BOUND:
        values.DEFAULT_PATCH_UPPER_BOUND = values.CONF_MAX_BOUND
    if values.CONF_LOW_BOUND:
        values.DEFAULT_PATCH_LOWER_BOUND = values.CONF_LOW_BOUND
    if values.CONF_MAX_FORK:
        values.DEFAULT_MAX_FORK = values.CONF_MAX_FORK
    if values.CONF_GEN_SEARCH_LIMIT:
        values.DEFAULT_GEN_SEARCH_LIMIT = values.CONF_GEN_SEARCH_LIMIT
    if values.CONF_ITERATION_LIMIT:
        values.DEFAULT_ITERATION_LIMIT = values.CONF_ITERATION_LIMIT
    if values.CONF_STACK_SIZE:
        values.DEFAULT_STACK_SIZE = values.CONF_STACK_SIZE
    if values.CONF_IS_CRASH:
        values.IS_CRASH = values.CONF_IS_CRASH
    sys.setrecursionlimit(values.DEFAULT_STACK_SIZE)
    load_component_list()


def initialize():
    emitter.title("Initializing Program")
    program_path = values.CONF_PATH_PROGRAM
    extractor.extract_byte_code(program_path)
    test_input_list = values.CONF_TEST_INPUT
    second_var_list = list()
    directory_path = "/".join(str(program_path).split("/")[:-1])
    klee_out_dir = directory_path + "/klee-last"
    for argument_list in test_input_list:
        emitter.sub_title("Running concrete execution for test case: " + str(argument_list))
        emitter.debug("input list in test case:" + argument_list)
        argument_list = str(argument_list).split(" ")
        values.ARGUMENT_LIST = argument_list
        exit_code = run_concrete_execution(program_path + ".bc", argument_list, True)
        assert exit_code == 0
        # set location of bug/crash
        if not values.CONF_LOC_CRASH:
            values.CONF_LOC_CRASH = reader.collect_crash_point(values.FILE_MESSAGE_LOG)
            if values.CONF_LOC_CRASH:
                values.IS_CRASH = True
                emitter.success("\t\t\t[info] identified crash location: " + str(values.CONF_LOC_CRASH))
        if values.IS_CRASH:
            arg_list, var_list = generator.generate_angelic_val_for_crash(klee_out_dir)
            for var in var_list:
                var_name = var["identifier"]
                if "angelic" in var_name:
                    second_var_list.append(var)
        emitter.sub_title("Running concolic execution for test case: " + str(argument_list))
        exit_code = run_concolic_execution(program_path + ".bc", argument_list, second_var_list, True)
        assert exit_code == 0
        if values.IS_CRASH:
            values.MASK_BYTE_LIST = generator.generate_mask_bytes(klee_out_dir)
        distance.update_distance_map()


def main(arg_list):
    global time_info, time_check, start_time
    create_directories()
    emitter.start()
    start_time = time.time()

    time_check = time.time()
    bootstrap(arg_list)
    duration = format((time.time() - time_check) / 60, '.3f')
    time_info[definitions.KEY_DURATION_BOOTSTRAP] = str(duration)

    time_check = time.time()
    if not values.CONF_SKIP_BUILD:
        builder.build_normal()
        assert os.path.isfile(values.CONF_PATH_PROGRAM)
        assert os.path.getsize(values.CONF_PATH_PROGRAM) > 0
    duration = format((time.time() - time_check) / 60, '.3f')
    time_info[definitions.KEY_DURATION_BUILD] = str(duration)

    time_check = time.time()
    if not values.CONF_SKIP_TEST:
        initialize()
    duration = format((time.time() - time_check) / 60, '.3f')
    time_info[definitions.KEY_DURATION_INITIALIZATION] = str(duration)

    time_check = time.time()
    repair.run(values.CONF_PATH_PROJECT, values.CONF_PATH_PROGRAM)
    duration = format(((time.time() - time_check) / 60 - float(values.TIME_TO_GENERATE)), '.3f')
    time_info[definitions.KEY_DURATION_REPAIR] = str(duration)

    # Final running time and exit message
    duration = format((time.time() - start_time) / 60, '.3f')
    time_info[definitions.KEY_DURATION_TOTAL] = str(duration)
    emitter.end(time_info)
    logger.end(time_info)


if __name__ == "__main__":
    global time_check, start_time, time_info
    import sys
    try:
        main(sys.argv[1:])
    except KeyboardInterrupt as e:
        parallel.pool.terminate()
        os.system("ps -aux | grep 'python' | awk '{print $2}' | xargs kill -9")
        error_exit("Program Interrupted by User")

        duration = format(((time.time() - time_check) / 60 - float(values.TIME_TO_GENERATE)), '.3f')
        time_info[definitions.KEY_DURATION_REPAIR] = str(duration)

        # Final running time and exit

        duration = format((time.time() - start_time) / 60, '.3f')
        time_info[definitions.KEY_DURATION_TOTAL] = str(duration)
        emitter.end(time_info)
        logger.end(time_info)
