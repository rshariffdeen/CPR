#! /usr/bin/env python3
# -*- coding: utf-8 -*-
import os

TOOL_NAME = "CPR"
DEBUG = False
ARGUMENT_LIST = []
SECOND_VAR_LIST = []
MASK_BYTE_LIST = dict()
SPECIFICATION_TXT = ""
TEST_SPECIFICATION = ""
ITERATION_NO = 0
COUNT_COMPONENTS_GEN = 0
COUNT_COMPONENTS_CUS = 0
COUNT_COMPONENTS = 0
COUNT_PATCH_GEN = 0
COUNT_PATCH_START = 0
COUNT_PATCH_END_SEED = 0
COUNT_PATCH_END = 0
COUNT_TEMPLATE_GEN = 0
COUNT_TEMPLATE_START = 0
COUNT_TEMPLATE_END_SEED = 0
COUNT_TEMPLATE_END = 0
COUNT_PATHS_EXPLORED = 0
COUNT_PATHS_DETECTED = 0
COUNT_PATHS_SKIPPED = 0
COUNT_HIT_PATCH_LOC = 0
COUNT_HIT_BUG_LOG = 0
COUNT_HIT_CRASH_LOC = 0
COUNT_HIT_CRASH = 0
IS_CRASH = False
IS_DISABLE_DISTANCE_CAL = True
IS_PATCH_BOOL = False
TIME_TO_GENERATE = 0
TIME_TO_EXPLORE = 0
TIME_TO_REDUCE = 0

LIST_PATCHES = []
LIST_TRACE = None
LIST_PPC = []
LIST_GENERATED_PATH = []
LIST_COMPONENTS = None
LIST_RELATIONSHIP_VAR = []
MAP_LOC_DISTANCE = dict()
LIST_KLEE_ASSUMPTIONS = []
LIST_BIT_LENGTH = dict()
LIST_PATH_CHECK = []
LIST_PATH_READ = []
LIST_PATCH_SCORE = dict()
LIST_PATCH_OVERAPPROX_CHECK = dict()
LIST_PATCH_UNDERAPPROX_CHECK = dict()
LIST_PATCH_SPACE = dict()
VALID_INPUT_SPACE = None
LIST_SEED_INPUT = []
LIST_SEED_FILES = []
LIST_TEST_INPUT = []
LIST_TEST_OUTPUT = []
LIST_TEST_FILES = dict()
LIST_PATCH_RANKING = dict()
MAP_PROG_VAR = dict()

PREFIX_PPC_STR = ""
PREFIX_PPC_FORMULA = None
NEGATED_PPC_FORMULA = None
LAST_PPC_FORMULA = None
SELECTED_PATCH = None


# ------------------ File Path Values ---------------
FILE_TRACE_LOG = ""
FILE_PPC_LOG = ""
FILE_EXPR_LOG = ""
FILE_POC_SYM = ""
FILE_POC_GEN = ""
FILE_POC_SEED = ""
FILE_MESSAGE_LOG = ""


# ------------------ Default Values ---------------
DEFAULT_DEPTH = 3
DEFAULT_ITERATION_LIMIT = -1
DEFAULT_PATCH_RANK_LIMIT = 5
DEFAULT_PATCH_LOWER_BOUND = -10
DEFAULT_PATCH_UPPER_BOUND = 10
DEFAULT_INPUT_LOWER_BOUND = -2147483648
DEFAULT_INPUT_UPPER_BOUND = 2147483647
DEFAULT_MAX_FORK = 5
DEFAULT_MAX_FORK_CEGIS = 100
DEFAULT_GEN_SEARCH_LIMIT = 40
DEFAULT_STACK_SIZE = 15000
DEFAULT_TIMEOUT_UNSAT = 10
DEFAULT_TIMEOUT_SAT = 10
DEFAULT_TIMEOUT_KLEE = 600
DEFAULT_TIMEOUT_KLEE_CEGIS = 3000
DEFAULT_TIMEOUT_CEGIS_EXPLORE = 30
DEFAULT_TIMEOUT_CEGIS_REFINE = 30
DEFAULT_TIME_DURATION = 60
DEFAULT_SELECTION_STRATEGY = "deterministic"
DEFAULT_DISTANCE_METRIC = "control-loc"
DEFAULT_PATCH_TYPE = "abstract"
DEFAULT_REFINE_METHOD = "under-approx"
DEFAULT_OPERATION_MODE = "parallel"
DEFAULT_REDUCE_METHOD = "cpr"
DEFAULT_COLLECT_STAT = False
DEFAULT_GEN_SPECIAL_PATH = True

IS_TAUTOLOGIES_INCLUDED = True
IS_CONTRADICTIONS_INCLUDED = True
crash_word_list = ["abort", "core dumped", "crashed", "exception"]
error_word_list = ["runtime error", "buffer-overflow", "unsigned integer overflow"]


# ---------------- Option Values ---------------------
OPTIONS_DIST_METRIC = {0: "control-loc", 1: "statement", 2: "angelic"}
OPTIONS_SELECT_METHOD = {0: "deterministic", 1: "random"}
OPTIONS_PATCH_TYPE = {0: "concrete", 1: "abstract"}
OPTIONS_OPERATION_MODE = {0: "sequential", 1: "semi-parallel", 2: "parallel"}
OPTIONS_REFINE_METHOD = {0: "under-approx", 1: "over-approx", 2: "overfit", 3: "none"}
OPTIONS_REDUCE_METHOD = {0: "cpr", 1: "cegis"}


# ------------------ Configuration Values ---------------
CONF_PATH_PROJECT = ""
CONF_PATH_SPECIFICATION = ""
CONF_PATH_PROGRAM = ""
CONF_COMMAND_CONFIG = None
CONF_COMMAND_BUILD = None
CONF_FLAG_ASAN = ""
CONF_FLAGS_C = ""
CONF_FLAGS_CXX = ""
CONF_GENERAL_COMP_LIST = ""
CONF_CUSTOM_COMP_LIST = ""
CONF_DEPTH_VALUE = ""
FILE_CONFIGURATION = ""
silence_emitter = False
CONF_DIR_SRC = ""
CONF_LOC_BUG = ""
CONF_LOC_LIST_CRASH = []
CONF_LOC_PATCH = ""
CONF_PATH_POC = ""
CONF_PATH_SEED = ""
CONF_LOW_BOUND = ""
CONF_MAX_BOUND = ""
CONF_MAX_FORK = ""
CONF_TAG_ID = ""
CONF_STATIC = False
CONF_GEN_SEARCH_LIMIT = ""
CONF_ITERATION_LIMIT = -1
CONF_SELECTION_STRATEGY = ""
CONF_DISTANCE_METRIC = ""
CONF_PATCH_TYPE = ""
CONF_REFINE_METHOD = ""
CONF_SKIP_BUILD = False
CONF_SKIP_GEN = False
CONF_SKIP_TEST = False
CONF_ONLY_TEST = False
CONF_ONLY_GEN = False
CONF_BUILD_FLAGS = ""
CONF_KLEE_FLAGS = ""
CONF_OPERATION_MODE = ""
CONF_STACK_SIZE = ""
CONF_MASK_ARG = ""
CONF_IS_CPP = False
CONF_IS_CRASH = False
CONF_REDUCE_METHOD = ""
CONF_ALL_COMPS = False
CONF_TIME_DURATION = 0
CONF_TIME_CEGIS_EXPLORE = 0
CONF_TIME_CEGIS_REFINE = 0
CONF_TIME_SPLIT = None
CONF_TIME_CHECK = None
CONF_TIMEOUT_SAT = None
CONF_TIMEOUT_KLEE = None
CONF_RANK_LIMIT = -1
CONF_TEST_INPUT_DIR = ""
CONF_TEST_OUTPUT_DIR = ""
CONF_TEST_INPUT_FILE = ""
CONF_TEST_OUTPUT_FILE = ""
CONF_TEST_INPUT_LIST = ""
CONF_TEST_OUTPUT_LIST = ""
CONF_TEST_BINARY_LIST = []
CONF_SEED_BINARY_LIST = []
CONF_TEST_SUITE_ID_LIST = []
CONF_SEED_SUITE_ID_LIST = []
CONF_TEST_SUITE_CONFIG = None
CONF_SEED_SUITE_CONFIG = None

CONF_SEED_FILE = ""
CONF_SEED_DIR = ""
CONF_SEED_LIST = ""
CONF_COLLECT_STAT = False
CONF_GEN_PATH_SPECIAL = None
CONF_ARG_PASS = False

