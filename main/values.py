#! /usr/bin/env python3
# -*- coding: utf-8 -*-
import os

TOOL_NAME = "ConRepair"
DEBUG = False
ARGUMENT_LIST = []
SECOND_VAR_LIST = []
SPECIFICATION = ""
TEST_SPECIFICATION = ""
ITERATION_NO = 0
IS_CRASH = False
IS_DISABLE_DISTANCE_CAL = False
TIME_TO_GENERATE = 0


LIST_TRACE = None
LIST_PPC = None
LIST_GENERATED_PATH = None
LIST_COMPONENTS = None
LIST_RELATIONSHIP_VAR = []
MAP_LOC_DISTANCE = dict()
LIST_KLEE_ASSUMPTIONS = []
LIST_BIT_LENGTH = dict()

PREFIX_PPC_STR = ""
PREFIX_PPC_FORMULA = None


# ------------------ File Path Values ---------------
FILE_TRACE_LOG = ""
FILE_PPC_LOG = ""
FILE_EXPR_LOG = ""
FILE_POC_SYM = ""
FILE_POC_GEN = ""
FILE_MESSAGE_LOG = ""


# ------------------ Default Values ---------------
DEFAULT_DEPTH = 3
DEFAULT_LOWER_BOUND = -10
DEFAULT_UPPER_BOUND = 11
DEFAULT_MAX_FORK = 5
DEFAULT_GEN_SEARCH_LIMIT = 40
crash_word_list = ["abort", "core dumped", "crashed", "exception"]
error_word_list = ["runtime error", "buffer-overflow", "unsigned integer overflow"]


# ---------------- Option Values ---------------------
OPTIONS_DIST_METRIC = {0: "control-loc", 1: "statement"}
OPTIONS_SELECT_METHOD = {0: "deterministic", 1: "random"}
OPTIONS_PATCH_TYPE = {0: "concrete", 1: "abstract"}


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
CONF_LOC_BUG = ""
CONF_PATH_POC = ""
CONF_LOW_BOUND = ""
CONF_MAX_BOUND = ""
CONF_MAX_FORK = ""
CONF_TAG_ID = ""
CONF_STATIC = False
CONF_LOC_PATCH = ""
CONF_SELECTION_STRATEGY = "deterministic"
CONF_DISTANCE_METRIC = "control-loc"
CONF_PATCH_TYPE = "concrete"
CONF_SKIP_BUILD = False
