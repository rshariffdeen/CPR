# -*- coding: utf-8 -*-

import sys
import os
from main import definitions, values, logger
import textwrap
from main.synthesis import program_to_code

rows, columns = os.popen('stty size', 'r').read().split()

GREY = '\t\x1b[1;30m'
RED = '\t\x1b[1;31m'
GREEN = '\x1b[1;32m'
YELLOW = '\t\x1b[1;33m'
BLUE = '\t\x1b[1;34m'
ROSE = '\t\x1b[1;35m'
CYAN = '\x1b[1;36m'
WHITE = '\t\x1b[1;37m'

PROG_OUTPUT_COLOR = '\t\x1b[0;30;47m'
STAT_COLOR = '\t\x1b[0;32;47m'


def write(print_message, print_color, new_line=True, prefix=None, indent_level=0):
    if not values.silence_emitter:
        message = "\033[K" + print_color + str(print_message) + '\x1b[0m'
        if prefix:
            prefix = "\033[K" + print_color + str(prefix) + '\x1b[0m'
            len_prefix = ((indent_level+1) * 4) + len(prefix)
            wrapper = textwrap.TextWrapper(initial_indent=prefix, subsequent_indent=' '*len_prefix, width=int(columns))
            message = wrapper.fill(message)
        sys.stdout.write(message)
        if new_line:
            r = "\n"
            sys.stdout.write("\n")
        else:
            r = "\033[K\r"
            sys.stdout.write(r)
        sys.stdout.flush()


def title(title):
    write("\n" + "="*100 + "\n\n\t" + title + "\n" + "="*100+"\n", CYAN)
    logger.information(title)


def sub_title(subtitle):
    write("\n\t" + subtitle + "\n\t" + "_"*90+"\n", CYAN)
    logger.information(subtitle)


def sub_sub_title(sub_title):
    write("\n\t\t" + sub_title + "\n\t\t" + "-"*90+"\n", CYAN)
    logger.information(sub_title)


def command(message):
    prefix = "\t\t[command] "
    write(message, ROSE, prefix=prefix, indent_level=2)
    logger.command("[command]" + message)


def debug(message, info=None):
    if values.DEBUG:
        prefix = "\t\t[debug] "
        write(message, GREY, prefix=prefix, indent_level=2)
        if info:
            write(info, GREY, prefix=prefix, indent_level=2)
    logger.debug(message)


def data(message, info=None):
    if values.DEBUG:
        prefix = "\t\t[data] "
        write(message, GREY, prefix=prefix, indent_level=2)
        if info:
            write(info, GREY, prefix=prefix, indent_level=2)
    logger.data(message)


def normal(message, jump_line=True):
    write(message, BLUE, jump_line)
    message = "[LOG]" + message
    logger.output(message)


def highlight(message, jump_line=True):
    indent_length = message.count("\t")
    prefix = "\t" * indent_length
    message = message.replace("\t", "")
    write(message, WHITE, jump_line, indent_level=indent_length, prefix=prefix)


def emit_patch(patch_tree, jump_line=True, message=""):
    output = message
    for (lid, prog) in patch_tree.items():
        code = lid + ": " + (program_to_code(prog))
    indent_length = 0
    prefix = "\t" * indent_length
    output = output + code
    write(output, WHITE, jump_line, indent_level=indent_length, prefix=prefix)


def information(message, jump_line=True):
    if values.DEBUG:
        write(message, GREY, jump_line)
    logger.information(message)


def statistics(message):
    write(message, WHITE)
    logger.output(message)


def error(message):
    write(message, RED)
    logger.error(message)


def success(message):
    write(message, GREEN)
    logger.output(message)


def special(message):
    write(message, ROSE)
    logger.output(message)


def program_output(output_message):
    write("\t\tProgram Output:", WHITE)
    if type(output_message) == list:
        for line in output_message:
            write("\t\t\t" + line.strip(), PROG_OUTPUT_COLOR)
    else:
        write("\t\t\t" + output_message, PROG_OUTPUT_COLOR)


def emit_var_map(var_map):
    write("\t\tVar Map:", WHITE)
    for var_a in var_map:
        highlight("\t\t\t " + var_a + " ==> " + var_map[var_a])


def emit_ast_script(ast_script):
    write("\t\tAST Script:", WHITE)
    for line in ast_script:
        special("\t\t\t " + line.strip())


def warning(message):
    write(message, YELLOW)
    logger.warning(message)


def note(message):
    write(message, WHITE)
    logger.note(message)


def start():
    logger.create()
    write("\n" + "#"*100 + "\n", BLUE)
    write("\t" + values.TOOL_NAME + " - Concolic Repair", BLUE)
    write("\tAutomated Program Repair Tool", BLUE)
    write("\tCopyright National University of Singapore", BLUE)
    write("\n" + "#" * 100, BLUE)


def end(time_info):
    statistics("\nRun time statistics:\n-----------------------\n")
    statistics("Startup: " + time_info[definitions.KEY_DURATION_BOOTSTRAP].format() + " minutes")
    statistics("Build: " + time_info[definitions.KEY_DURATION_BUILD] + " minutes")
    statistics("Initialization: " + time_info[definitions.KEY_DURATION_INITIALIZATION] + " minutes")
    statistics("Generation: " + values.TIME_TO_GENERATE + " minutes")
    statistics("Repair: " + time_info[definitions.KEY_DURATION_REPAIR] + " minutes")
    statistics("Iteration Count: " + str(values.ITERATION_NO))
    statistics("Patch Start Count: " + str(values.COUNT_PATCH_START))
    statistics("Patch End Count: " + str(values.COUNT_PATCH_END))
    statistics("Component Count: " + str(values.COUNT_COMPONENTS))
    statistics("Gen Limit: " + str(values.DEFAULT_GEN_SEARCH_LIMIT))
    success("\n" + values.TOOL_NAME + " finished successfully after " + time_info[definitions.KEY_DURATION_TOTAL] + " minutes \n")


def help():
    write("Usage: python3.6 ConRepair.py [OPTIONS] " + definitions.ARG_CONF_FILE + "$FILE_PATH", RED)
    write("Options are:", RED)
    write("\t" + definitions.ARG_DEBUG + "\t| " + "enable debugging information", RED)
    write("\t" + definitions.ARG_DISABLE_DISTANCE_CAL + "\t| " + "disable distance calculation (default=enabled)", RED)
    write("\t" + definitions.ARG_SELECTION_METHOD + "\t| " + "selection strategy [0: deterministic, 1: random] (default=0)", RED)
    write("\t" + definitions.ARG_DIST_METRIC + "\t| " + "distance metric [0: control-loc, 1: statement] (default=0)", RED)
    write("\t" + definitions.ARG_PATCH_TYPE + "\t| " + "patch type [0: concrete, 1: abstract] (default=0)", RED)
