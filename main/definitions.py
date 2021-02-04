#! /usr/bin/env python3
# -*- coding: utf-8 -*-
import os

# ------------------- Directories --------------------

DIRECTORY_ROOT = "/".join(os.path.realpath(__file__).split("/")[:-2])
DIRECTORY_LIB = DIRECTORY_ROOT + "/lib"
DIRECTORY_LOG = DIRECTORY_ROOT + "/logs"
DIRECTORY_LOG_BASE = DIRECTORY_ROOT + "/logs"
DIRECTORY_TESTS = DIRECTORY_ROOT + "/tests"
DIRECTORY_OUTPUT_BASE = DIRECTORY_ROOT + "/output"
DIRECTORY_COMPONENTS = DIRECTORY_ROOT + "/components"
DIRECTORY_OUTPUT = ""
DIRECTORY_TMP = DIRECTORY_ROOT + "/tmp"
DIRECTORY_BACKUP = DIRECTORY_ROOT + "/backup"
DIRECTORY_TOOLS = DIRECTORY_ROOT + "/tools"
DIRECTORY_DATA = DIRECTORY_ROOT + "/data"

# ------------------- Files --------------------

FILE_MAIN_LOG = ""
FILE_ERROR_LOG = DIRECTORY_LOG + "/log-error"
FILE_LAST_LOG = DIRECTORY_LOG + "/log-latest"
FILE_MAKE_LOG = DIRECTORY_LOG + "/log-make"
FILE_COMMAND_LOG = DIRECTORY_LOG + "/log-command"
FILE_STANDARD_FUNCTION_LIST = DIRECTORY_DATA + "/standard-function-list"
FILE_STANDARD_MACRO_LIST = DIRECTORY_DATA + "/standard-macro-list"
FILE_PATCH_SET = ""
FILE_TRIDENT_LIB_BCA = DIRECTORY_LIB + "/libtrident_runtime.bca"

# ------------------- Configuration --------------------

CONF_PATH_PROJECT = "project_path:"
CONF_PATH_SPECIFICATION = "spec_path:"
CONF_PATH_POC = "poc_path:"
CONF_COMMAND_CONFIG = "config_command:"
CONF_COMMAND_BUILD = "build_command:"
CONF_BINARY_PATH = "binary_path:"
CONF_TEST_INPUT_LIST = "test_input:"
CONF_TEST_OUTPUT_LIST = "test_output:"
CONF_FILE_SEED_LIST = "file_seed_list:"
CONF_GENERAL_COMP_LIST = "general_comp_list:"
CONF_CUSTOM_COMP_LIST = "custom_comp_list:"
CONF_DEPTH_VALUE = "depth:"
CONF_DIR_SRC = "src_directory:"
CONF_LOC_BUG = "loc_bug:"
CONF_LOC_PATCH = "loc_patch:"
CONF_LOW_BOUND = "low_bound:"
CONF_MAX_BOUND = "max_bound:"
CONF_GEN_SEARCH_LIMIT = "gen_limit:"
CONF_MAX_FORK = "max-fork:"
CONF_TAG_ID = "tag_id:"
CONF_STATIC = "static:"
CONF_FLAG_ASAN = "flag_asan:"
CONF_FLAGS_C = "flag_c:"
CONF_FLAGS_CXX = "flag_cxx:"
CONF_SELECTION_STRATEGY = "select_strategy:"
CONF_DISTANCE_METRIC = "dist_metric:"
CONF_PATCH_TYPE = "patch_type:"
CONF_BUILD_FLAGS = "build_flags:"
CONF_KLEE_FLAGS = "klee_flags:"
CONF_OPERATION_MODE = "mode:"
CONF_ITERATION_LIMIT = "iterations:"
CONF_STACK_SIZE = "stack_size:"
CONF_MASK_ARG = "mask_arg:"
CONF_IS_CPP = "is_cpp:"
CONF_IS_CRASH = "is_crash:"
CONF_TIMEOUT_SAT = "timeout_sat:"
CONF_TIMEOUT_KLEE = "timeout_klee:"
CONF_RANK_LIMIT = "rank_limit:"


# ----------------- KEY DEFINITIONS -------------------

KEY_DURATION_TOTAL = 'run-time'
KEY_DURATION_BOOTSTRAP = 'bootstrap'
KEY_DURATION_BUILD = "build"
KEY_DURATION_INITIALIZATION = 'initialization'
KEY_DURATION_REPAIR = "repair"


# ---------------- ARGUMENTS ---------------------------
ARG_CONF_FILE = "--conf="
ARG_DEBUG = "--debug"
ARG_DISABLE_DISTANCE_CAL = "--dist-cal="
ARG_DIST_METRIC = "--dist-metric="
ARG_SELECTION_METHOD = "--selection="
ARG_OPERATION_MODE = "--mode="
ARG_PATCH_TYPE = "--patch-type="
ARG_REFINE_METHOD = "--refine-method="
ARG_SKIP_BUILD = "--skip-build"
ARG_SKIP_GENERATION = "--skip-gen"
ARG_SKIP_TEST = "--skip-test"
ARG_REDUCE_METHOD = "--reduce-method="
ARG_COMP_ALL = "--all-comps"
ARG_CEGIS_TIME_SPLIT = "--cegis-time-split="
ARG_TIME_DURATION = "--time-duration="
ARG_RANK_LIMIT = "--top-n="
ARG_ITERATION_COUNT = "--iterations="


# ----------------- TOOLS --------------------------------
TOOL_VECGEN = "third-party/deckard/cvecgen_fail "
TOOL_VECGEN_ORIG = "third-party/deckard/cvecgen "

PATCH_COMMAND = "patchweave-patch"
PATCH_SIZE = "1000"
DIFF_COMMAND = "crochet-diff "
DIFF_SIZE = "1000"
SYNTAX_CHECK_COMMAND = "clang-check "
STYLE_FORMAT_COMMAND = "clang-format -style=LLVM "

crash_word_list = ["abort", "core dumped", "crashed", "exception"]
error_word_list = ["runtime error", "buffer-overflow", "unsigned integer overflow"]
