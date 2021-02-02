import os
import shutil
import time
import traceback
import signal
from pathlib import Path
from main import emitter, logger, definitions, values, builder, repair, \
    configuration, reader, distance, synthesis, parallel, extractor, generator
from main.utilities import error_exit
from main.concolic import run_concrete_execution, run_concolic_execution

start_time = 0
time_info = {
    definitions.KEY_DURATION_INITIALIZATION: '0',
    definitions.KEY_DURATION_BUILD: '0',
    definitions.KEY_DURATION_BOOTSTRAP: '0',
    definitions.KEY_DURATION_REPAIR: '0',
    definitions.KEY_DURATION_TOTAL: '0'
    }


def create_directories():
    if not os.path.isdir(definitions.DIRECTORY_LOG):
        os.makedirs(definitions.DIRECTORY_LOG)

    if not os.path.isdir(definitions.DIRECTORY_OUTPUT_BASE):
        os.makedirs(definitions.DIRECTORY_OUTPUT_BASE)

    if not os.path.isdir(definitions.DIRECTORY_BACKUP):
        os.makedirs(definitions.DIRECTORY_BACKUP)

    if not os.path.isdir(definitions.DIRECTORY_TMP):
        os.makedirs(definitions.DIRECTORY_TMP)


def timeout_handler(signum, frame):
    emitter.error("TIMEOUT Exception")
    raise Exception("end of time")


def bootstrap(arg_list):
    emitter.title("Starting " + values.TOOL_NAME + " (CardioPulmonary Resuscitation) ")
    emitter.sub_title("Loading Configurations")
    configuration.read_conf(arg_list)
    configuration.read_conf_file()
    configuration.update_configuration()
    configuration.print_configuration()
    configuration.load_component_list()


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
        argument_list = extractor.extract_input_arg_list(argument_list)

        values.ARGUMENT_LIST = argument_list
        exit_code = run_concrete_execution(program_path + ".bc", argument_list, True)
        assert exit_code == 0
        # set location of bug/crash
        if not values.CONF_LOC_CRASH:
            values.CONF_LOC_CRASH = reader.collect_crash_point(values.FILE_MESSAGE_LOG)
            if values.CONF_LOC_CRASH:
                values.IS_CRASH = True
                emitter.success("\t\t\t[info] identified crash location: " + str(values.CONF_LOC_CRASH))
        # if values.IS_CRASH:
        #     arg_list, var_list = generator.generate_angelic_val_for_crash(klee_out_dir)
        #     for var in var_list:
        #         var_name = var["identifier"]
        #         if "angelic" in var_name:
        #             second_var_list.append(var)
        # emitter.sub_title("Running concolic execution for test case: " + str(argument_list))
        # exit_code = run_concolic_execution(program_path + ".bc", argument_list, second_var_list, True)
        # assert exit_code == 0
        # if values.IS_CRASH:
        #     values.MASK_BYTE_LIST = generator.generate_mask_bytes(klee_out_dir)
        # distance.update_distance_map()


def run(arg_list):
    global start_time, time_info
    create_directories()
    logger.create()
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


if __name__ == "__main__":
    import sys
    is_error = False
    signal.signal(signal.SIGALRM, timeout_handler)
    try:
        run(sys.argv[1:])
    except KeyboardInterrupt as e:
        parallel.pool.terminate()
        logger.error(traceback.format_exc())
        is_error = True
    except Exception as e:
        emitter.error("Runtime Error")
        emitter.error(str(e))
        logger.error(traceback.format_exc())
        is_error = True
    finally:
        # Final running time and exit message
        # os.system("ps -aux | grep 'python' | awk '{print $2}' | xargs kill -9")
        total_duration = format((time.time() - start_time) / 60, '.3f')
        time_info[definitions.KEY_DURATION_TOTAL] = str(total_duration)
        emitter.end(time_info, is_error)
        logger.end(time_info, is_error)
        logger.store()
