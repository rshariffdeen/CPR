#! /usr/bin/env python3
# -*- coding: utf-8 -*-
import os

TOOL_NAME = "ConRepair"
DEBUG = False
ARGUMENT_LIST = []
SECOND_VAR_LIST = []
SPECIFICATION = ""
TEST_SPECIFICATION = ""

LIST_TRACE = None
LIST_PPC = None
MAP_LOC_DISTANCE = dict()



# ------------------ File Path Values ---------------
FILE_TRACE_LOG = ""
FILE_PPC_LOG = ""
FILE_EXPR_LOG = ""


# ------------------ Default Values ---------------
DEFAULT_DEPTH = 3
DEFAULT_LOWER_BOUND = -10
DEFAULT_UPPER_BOUND = 11
crash_word_list = ["abort", "core dumped", "crashed", "exception"]
error_word_list = ["runtime error", "buffer-overflow", "unsigned integer overflow"]


# ------------------ Configuration Values ---------------
CONF_PATH_PROJECT = ""
CONF_PATH_SPECIFICATION = ""
CONF_PATH_PROGRAM = ""
CONF_COMMAND_CONFIG = None
CONF_COMMAND_BUILD = None
CONF_FLAG_ASAN = ""
CONF_FLAGS_C = ""
CONF_FLAGS_CXX = ""
CONF_TEST_FILE = ""
CONF_TEST_INPUT = ""
CONF_TEST_OUTPUT = ""
CONF_GENERAL_COMP_LIST = ""
CONF_CUSTOM_COMP_LIST = ""
CONF_DEPTH_VALUE = ""
FILE_CONFIGURATION = ""
silence_emitter = False
CONF_DIR_SRC = ""
CONF_BUG_LOCATION = ""
CONF_PATH_POC = ""
