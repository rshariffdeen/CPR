# -*- coding: utf-8 -*-

import sys
from main import definitions, values, logger


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


def write(print_message, print_color, new_line=True):
    if not values.silence_emitter:
        r = "\033[K" + print_color + str(print_message) + '\x1b[0m'
        sys.stdout.write(r)
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
    message = "\t[command] " + message
    write(message, ROSE)
    logger.command(message)


def debug(prefix, message):
    if values.DEBUG:
        prefix = "\t[debug] " + prefix
        message = "\t[debug] " + str(message)
        write(prefix, GREY)
        write(message, GREY)
    logger.command(message)


def normal(message, jump_line=True):
    write(message, BLUE, jump_line)
    # Logger.output(message)


def highlight(message, jump_line=True):
    write(message, WHITE, jump_line)


def information(message, jump_line=True):
    if values.DEBUG:
        write(message, GREY, jump_line)
    logger.information(message)


def statistics(message):
    write(message, GREY)
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


def start():
    logger.create()
    write("\n" + "#"*100 + "\n", BLUE)
    write("\t" + values.TOOL_NAME + " - Concolic Repair", BLUE)
    write("\tAutomated Program Repair Tool", BLUE)
    write("\tCopyright National University of Singapore", BLUE)
    write("\n" + "#" * 100, BLUE)


def end(time_info):
    statistics("\nRun time statistics:\n-----------------------\n")
    statistics("Startup: " + time_info[definitions.KEY_DURATION_BOOTSTRAP] + " seconds")
    statistics("Build: " + time_info[definitions.KEY_DURATION_BUILD] + " seconds")
    statistics("Initialization: " + time_info[definitions.KEY_DURATION_INITIALIZATION] + " seconds")
    statistics("Repair: " + time_info[definitions.KEY_DURATION_REPAIR] + " seconds")
    success("\n" + values.TOOL_NAME + " finished successfully after " + time_info[definitions.KEY_DURATION_TOTAL] + " seconds\n")


def help():
    write("Usage: python3.6 ConRepair.py [OPTIONS] " + definitions.ARG_CONF_FILE + "$FILE_PATH", RED)
    write("Options are:", RED)
    write("\t" + definitions.ARG_DEBUG + "\t| " + "enable debugging information", RED)

