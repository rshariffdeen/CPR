import os
import time
import traceback
import signal
import multiprocessing as mp

import app.configuration
import app.utilities
from app import emitter, logger, definitions, values, builder, repair, \
    configuration, reader, parallel, extractor,  oracle
from app.concolic import run_concrete_execution

start_time = 0
time_info = {
    definitions.KEY_DURATION_INITIALIZATION: '0',
    definitions.KEY_DURATION_BUILD: '0',
    definitions.KEY_DURATION_BOOTSTRAP: '0',
    definitions.KEY_DURATION_REPAIR: '0',
    definitions.KEY_DURATION_TOTAL: '0'
    }

stop_event = mp.Event()


def create_directories():
    if not os.path.isdir(definitions.DIRECTORY_LOG_BASE):
        os.makedirs(definitions.DIRECTORY_LOG_BASE)

    if not os.path.isdir(definitions.DIRECTORY_OUTPUT_BASE):
        os.makedirs(definitions.DIRECTORY_OUTPUT_BASE)

    if not os.path.isdir(definitions.DIRECTORY_BACKUP):
        os.makedirs(definitions.DIRECTORY_BACKUP)

    if not os.path.isdir(definitions.DIRECTORY_TMP):
        os.makedirs(definitions.DIRECTORY_TMP)


def timeout_handler(signum, frame):
    emitter.error("TIMEOUT Exception")
    raise Exception("end of time")


def shutdown(signum, frame):
    global stop_event
    emitter.warning("Exiting due to Terminate Signal")
    stop_event.set()
    raise SystemExit


def bootstrap(arg_list):
    emitter.title("Starting " + values.TOOL_NAME + " (CardioPulmonary Resuscitation) ")
    emitter.sub_title("Loading Configurations")
    configuration.read_conf(arg_list)
    configuration.read_conf_file()
    configuration.update_configuration()

    configuration.collect_test_list()
    configuration.collect_seed_list()

    # configuration.collect_var_mapping()
    configuration.load_component_list()
    configuration.print_configuration()
    values.CONF_ARG_PASS = True
    app.utilities.check_budget(values.DEFAULT_TIME_DURATION)


def initialize():
    emitter.title("Initializing Program")
    test_input_list = values.LIST_TEST_INPUT
    second_var_list = list()
    output_dir_path = definitions.DIRECTORY_OUTPUT
    emitter.sub_title("Running Test-Suite")
    test_case_id = 0
    count_seeds = len(values.LIST_SEED_INPUT)
    count_inputs = len(test_input_list)
    for argument_list in test_input_list[:count_inputs - count_seeds]:
        print_argument_list = app.configuration.extract_input_arg_list(argument_list)
        generalized_arg_list = []
        seed_file = None
        test_case_id = test_case_id + 1
        for arg in print_argument_list:
            if arg in (list(values.LIST_SEED_FILES.values()) + list(values.LIST_TEST_FILES.values())):
                generalized_arg_list.append("$POC")
                seed_file = arg
            else:
                generalized_arg_list.append(arg)

        emitter.sub_sub_title("Test Case #" + str(test_case_id))
        emitter.highlight("\tUsing Arguments: " + str(generalized_arg_list))
        emitter.highlight("\tUsing Input File: " + str(seed_file))
        emitter.debug("input list in test case:" + argument_list)
        argument_list = app.configuration.extract_input_arg_list(argument_list)
        klee_out_dir = output_dir_path + "/klee-out-test-" + str(test_case_id - 1)
        if values.LIST_TEST_BINARY:
            program_path = values.LIST_TEST_BINARY[test_case_id - 1]
            values.CONF_PATH_PROGRAM = program_path
        else:
            program_path = values.CONF_PATH_PROGRAM
        emitter.highlight("\tUsing Binary: " + str(program_path))
        extractor.extract_byte_code(program_path)
        if not os.path.isfile(program_path + ".bc"):
            app.utilities.error_exit("Unable to generate bytecode for " + program_path)

        exit_code = run_concrete_execution(program_path + ".bc", argument_list, True, klee_out_dir)
        assert exit_code == 0
        # set location of bug/crash
        values.IS_CRASH = False
        latest_crash_loc = reader.collect_crash_point(values.FILE_MESSAGE_LOG)
        # if oracle.is_loc_in_trace(values.CONF_LOC_PATCH):
        #     values.USEFUL_SEED_ID_LIST.append(test_case_id)
        if latest_crash_loc:
            values.IS_CRASH = True
            emitter.success("\t\t\t[info] identified a crash location: " + str(latest_crash_loc))
            if latest_crash_loc not in values.CONF_LOC_LIST_CRASH:
                values.CONF_LOC_LIST_CRASH.append(latest_crash_loc)


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
        if values.CONF_PATH_PROGRAM:
            assert os.path.isfile(values.CONF_PATH_PROGRAM)
            assert os.path.getsize(values.CONF_PATH_PROGRAM) > 0
    duration = format((time.time() - time_check) / 60, '.3f')
    time_info[definitions.KEY_DURATION_BUILD] = str(duration)

    time_check = time.time()
    if not values.CONF_SKIP_TEST:
        initialize()
    duration = format((time.time() - time_check) / 60, '.3f')
    time_info[definitions.KEY_DURATION_INITIALIZATION] = str(duration)

    if values.CONF_ONLY_TEST:
        return
    time_check = time.time()
    repair.run(values.CONF_PATH_PROJECT, values.CONF_PATH_PROGRAM)
    duration = format(((time.time() - time_check) / 60 - float(values.TIME_TO_GENERATE)), '.3f')
    time_info[definitions.KEY_DURATION_REPAIR] = str(duration)


def main():
    import sys
    is_error = False
    signal.signal(signal.SIGALRM, timeout_handler)
    signal.signal(signal.SIGTERM, shutdown)
    try:
        run(sys.argv[1:])
    except SystemExit as e:
        total_duration = format((time.time() - start_time) / 60, '.3f')
        time_info[definitions.KEY_DURATION_TOTAL] = str(total_duration)
        emitter.end(time_info, is_error)
        logger.end(time_info, is_error)
        logger.store()
        parallel.pool.terminate()
        parallel.pool.join()
        # os.system("ps -aux | grep 'cpr' | awk '{print $2}' | xargs kill -9")
    except KeyboardInterrupt as e:
        total_duration = format((time.time() - start_time) / 60, '.3f')
        time_info[definitions.KEY_DURATION_TOTAL] = str(total_duration)
        emitter.end(time_info, is_error)
        logger.end(time_info, is_error)
        logger.store()
    except Exception as e:
        is_error = True
        emitter.error("Runtime Error")
        emitter.error(str(e))
        logger.error(traceback.format_exc())
    finally:
        # Final running time and exit message
        # os.system("ps -aux | grep 'python' | awk '{print $2}' | xargs kill -9")
        total_duration = format((time.time() - start_time) / 60, '.3f')
        time_info[definitions.KEY_DURATION_TOTAL] = str(total_duration)
        emitter.end(time_info, is_error)
        logger.end(time_info, is_error)
        logger.store()
        if is_error:
            exit(1)
        exit(0)
