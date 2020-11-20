import sys
import json
import subprocess
import os

KEY_BUG_ID = "bug_id"
KEY_BENCHMARK = "benchmark"
KEY_ID = "id"
KEY_SUBJECT = "subject"


ARG_DATA_PATH = "--data-dir="
ARG_TOOL_PATH = "--tool-path="
ARG_TOOL_NAME = "--tool-name="
ARG_TOOL_PARAMS = "--tool-param="
ARG_DEBUG_MODE = "--debug"
ARG_ONLY_SETUP = "--only-setup"
ARG_BUG_ID = "--bug-id="
ARG_START_ID = "--start-id="
ARG_SKIP_LIST = "--skip-list="

CONF_DATA_PATH = "/data"
CONF_TOOL_PATH = "/concolic-repair"
CONF_TOOL_PARAMS = "--mode=2"
CONF_TOOL_NAME = "python3.6 ConRepair.py"
CONF_DEBUG = False
CONF_BUG_ID = None
CONF_START_ID = None
CONF_SETUP_ONLY = False
CONF_SKIP_LIST = ["2","8","13","14","15","16","21"]

FILE_META_DATA = "meta-data"
FILE_ERROR_LOG = "error-log"


DIR_MAIN = os.getcwd()
DIR_LOGS = DIR_MAIN + "/logs"
DIR_RESULT = DIR_MAIN + "/result"
DIR_SCRIPT = DIR_MAIN + "/scripts"

EXPERIMENT_ITEMS = list()


def create_directories():
    if not os.path.isdir(DIR_LOGS):
        create_command = "mkdir " + DIR_LOGS
        execute_command(create_command)
    if not os.path.isdir(DIR_RESULT):
        create_command = "mkdir " + DIR_RESULT
        execute_command(create_command)


def execute_command(command):
    if CONF_DEBUG:
        print("\t[COMMAND]" + command)
    process = subprocess.Popen([command], stdout=subprocess.PIPE, shell=True)
    (output, error) = process.communicate()


def setup(script_path, script_name):
    global FILE_ERROR_LOG, CONF_DATA_PATH
    print("\t[INFO] running script for setup")
    script_command = "{ cd " + script_path + "; bash " + script_name + " " + CONF_DATA_PATH + ";} 2> " + FILE_ERROR_LOG
    execute_command(script_command)


def evaluate(conf_path, bug_id):
    global CONF_TOOL_PARAMS, CONF_TOOL_PATH, CONF_TOOL_NAME, DIR_LOGS
    print("\t[INFO]running evaluation")
    log_path = str(conf_path).replace(".conf", ".log")
    tool_command = "{ cd " + CONF_TOOL_PATH + ";" + CONF_TOOL_NAME + " --conf=" + conf_path + " "+ CONF_TOOL_PARAMS + ";} 2> " + FILE_ERROR_LOG
    execute_command(tool_command)
    exp_dir = DIR_RESULT + "/" + str(bug_id)
    mk_command = "mkdir " + exp_dir
    execute_command(mk_command)
    copy_output = "{ cp -rf " + CONF_TOOL_PATH + "/output/" + bug_id + " " + exp_dir + ";} 2> " + FILE_ERROR_LOG
    execute_command(copy_output)
    copy_log = "{ cp " + CONF_TOOL_PATH + "/logs/log-latest " + exp_dir + ";} 2> " + FILE_ERROR_LOG
    execute_command(copy_log)
    copy_log = "cp " + FILE_ERROR_LOG + " " + exp_dir
    execute_command(copy_log)


def load_experiment():
    global EXPERIMENT_ITEMS
    print("[DRIVER] Loading experiment data\n")
    with open(FILE_META_DATA, 'r') as in_file:
        json_data = json.load(in_file)
        EXPERIMENT_ITEMS = json_data


def read_arg():
    global CONF_DATA_PATH, CONF_TOOL_NAME, CONF_TOOL_PARAMS, CONF_START_ID
    global CONF_TOOL_PATH, CONF_DEBUG, CONF_SETUP_ONLY, CONF_BUG_ID, CONF_SKIP_LIST
    print("[DRIVER] Reading configuration values")
    if len(sys.argv) > 1:
        for arg in sys.argv:
            if ARG_DATA_PATH in arg:
                CONF_DATA_PATH = str(arg).replace(ARG_DATA_PATH, "")
            elif ARG_TOOL_NAME in arg:
                CONF_TOOL_NAME = str(arg).replace(ARG_TOOL_NAME, "")
            elif ARG_TOOL_PATH in arg:
                CONF_TOOL_PATH = str(arg).replace(ARG_TOOL_PATH, "")
            elif ARG_TOOL_PARAMS in arg:
                CONF_TOOL_PARAMS = str(arg).replace(ARG_TOOL_PARAMS, "")
            elif ARG_DEBUG_MODE in arg:
                CONF_DEBUG = True
            elif ARG_ONLY_SETUP in arg:
                CONF_SETUP_ONLY = True
            elif ARG_BUG_ID in arg:
                CONF_BUG_ID = int(str(arg).replace(ARG_BUG_ID, ""))
            elif ARG_START_ID in arg:
                CONF_START_ID = int(str(arg).replace(ARG_START_ID, ""))
            elif ARG_SKIP_LIST in arg:
                CONF_SKIP_LIST = str(arg).replace(ARG_SKIP_LIST, "").split(",")
            elif "driver.py" in arg:
                continue
            else:
                print("Unknown option: " + str(arg))
                print("Usage: python driver [OPTIONS] ")
                print("Options are:")
                print("\t" + ARG_DATA_PATH + "\t| " + "directory for experiments")
                print("\t" + ARG_TOOL_NAME + "\t| " + "name of the tool")
                print("\t" + ARG_TOOL_PATH + "\t| " + "path of the tool")
                print("\t" + ARG_TOOL_PARAMS + "\t| " + "parameters for the tool")
                print("\t" + ARG_DEBUG_MODE + "\t| " + "enable debug mode")
                exit()


def run():
    global EXPERIMENT_ITEMS, DIR_MAIN, CONF_DATA_PATH, CONF_TOOL_PARAMS
    print("[DRIVER] Running experiment driver")
    read_arg()
    load_experiment()
    create_directories()
    index = 1
    for experiment_item in EXPERIMENT_ITEMS:
        if CONF_BUG_ID and index != CONF_BUG_ID:
            index = index + 1
            continue
        if CONF_START_ID and index < CONF_START_ID:
            index = index + 1
            continue
        if CONF_SKIP_LIST and str(index) in CONF_SKIP_LIST:
            index = index + 1
            continue

        experiment_name = "Experiment-" + str(index) + "\n-----------------------------"
        print(experiment_name)
        bug_name = str(experiment_item[KEY_BUG_ID])
        subject_name = str(experiment_item[KEY_SUBJECT])
        benchmark = str(experiment_item[KEY_BENCHMARK])
        directory_name = benchmark + "/" + subject_name + "/" + bug_name
        script_name = "setup.sh"
        conf_file_name = "repair.conf"

        script_path = DIR_SCRIPT + "/" + directory_name
        deploy_path = CONF_DATA_PATH + "/" + directory_name + "/"
        deployed_conf_path = deploy_path + "/" + conf_file_name
        print("\t[META-DATA] benchmark: " + benchmark)
        print("\t[META-DATA] project: " + subject_name)
        print("\t[META-DATA] bug ID: " + bug_name)
        if not os.path.isfile(deployed_conf_path):
            setup(script_path, script_name)
        if not CONF_SETUP_ONLY:
            evaluate(deployed_conf_path, bug_name)
        index = index + 1


if __name__ == "__main__":
    try:
        run()
    except KeyboardInterrupt as e:
        print("[DRIVER] Program Interrupted by User")
        exit()
