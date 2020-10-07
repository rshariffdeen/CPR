# -*- coding: utf-8 -*-

import time
import datetime
import os
from main import definitions, values
from shutil import copyfile


def create():
    log_file_name = "log-" + str(time.time())
    log_file_path = definitions.DIRECTORY_LOG + "/" + log_file_name
    definitions.FILE_MAIN_LOG = log_file_path
    with open(definitions.FILE_MAIN_LOG, 'w+') as log_file:
        log_file.write("[Start] " + values.TOOL_NAME + " started at " + str(datetime.datetime.now()) + "\n")
    if os.path.exists(definitions.FILE_LAST_LOG):
        os.remove(definitions.FILE_LAST_LOG)
    if os.path.exists(definitions.FILE_ERROR_LOG):
        os.remove(definitions.FILE_ERROR_LOG)
    if os.path.exists(definitions.FILE_COMMAND_LOG):
        os.remove(definitions.FILE_COMMAND_LOG)
    with open(definitions.FILE_LAST_LOG, 'w+') as last_log:
        last_log.write("[Start] " + values.TOOL_NAME + " started at " + str(datetime.datetime.now()) + "\n")


def log(log_message):
    log_message = "[" + str(time.asctime()) + "]" + log_message
    if "COMMAND" in log_message:
        with open(definitions.FILE_COMMAND_LOG, 'a') as log_file:
            log_file.write(log_message)
    with open(definitions.FILE_MAIN_LOG, 'a') as log_file:
        log_file.write(log_message)
    with open(definitions.FILE_LAST_LOG, 'a') as log_file:
        log_file.write(log_message)


def information(message):
    message = "[INFO]: " + str(message) + "\n"
    log(message)


def trace(function_name, arguments):
    message = "[TRACE]: " + function_name + ": " + str(arguments.keys()) + "\n"
    log(message)


def command(message):
    message = "[COMMAND]: " + str(message) + "\n"
    log(message)


def data(message):
    message = "[DATA]: " + str(message) + "\n"
    log(message)


def debug(message):
    message = "[DEBUG]: " + str(message) + "\n"
    log(message)


def error(message):
    message = "[ERROR]: " + str(message) + "\n"
    log(message)


def note(message):
    message = "[NOTE]: " + str(message) + "\n"
    log(message)


def output(message):
    log(message + "\n")


def warning(message):
    message = "[WARNING]: " + str(message) + "\n"
    log(message)


def end(time_duration):
    output("[END] PatchWeave ended at " + str(datetime.datetime.now()) + "\n\n")
    output("\nTime duration\n----------------------\n\n")
    output("Startup: " + time_duration[definitions.KEY_DURATION_BOOTSTRAP] + " minutes")
    output("Build: " + time_duration[definitions.KEY_DURATION_BUILD] + " minutes")
    output("Initialization: " + time_duration[definitions.KEY_DURATION_INITIALIZATION] + " minutes")
    output("Generation: " + values.TIME_TO_GENERATE + " minutes")
    output("Repair: " + time_duration[definitions.KEY_DURATION_REPAIR] + " minutes")
    output("Iteration Count: " + str(values.ITERATION_NO))
    output("Patch Start Count: " + str(values.COUNT_PATCH_START))
    output("Patch End Count: " + str(values.COUNT_PATCH_END))
    output("Component Count: " + str(values.COUNT_COMPONENTS))
    output("Gen Limit: " + str(values.DEFAULT_GEN_SEARCH_LIMIT))
    output("\n" + values.TOOL_NAME + " finished successfully after " + time_duration[definitions.KEY_DURATION_TOTAL] + " minutes \n")
    copyfile(definitions.FILE_MAIN_LOG, definitions.DIRECTORY_OUTPUT + "/main-log")

