#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import os
import sys
from main.utilities import execute_command, error_exit
from main import definitions, values, logger, emitter

CC = "$TRIDENT_CC"
CXX = "$TRIDENT_CXX"
C_FLAGS = "-g -O0  -static -e"
CXX_FLAGS = "-g -O0 -static -e"
LD_FLAGS = "-L/concolic-repair/lib -ltrident_runtime -ltrident_proxy -lkleeRuntest"


def config_project(project_path, is_llvm, custom_config_command=None):
    emitter.sub_sub_title("configuring program")
    dir_command = "cd " + project_path + ";"
    if os.path.exists(project_path + "/" + "aclocal.m4"):
        pre_config_command = "rm aclocal.m4;aclocal"
        execute_command(pre_config_command)
    config_command = None
    if custom_config_command is not None:
        if custom_config_command == "skip":
            emitter.warning("\t[warning] skipping configuration")
            return
        else:
            if CC == "wllvm":
                custom_config_command = remove_fsanitize(custom_config_command)
                if "cmake" in custom_config_command:
                    custom_config_command = custom_config_command.replace("clang", "wllvm")
                    custom_config_command = custom_config_command.replace("clang++", "wllvm++")
                # print(custom_config_command)
            # config_command = "CC=" + CC + " "
            # config_command += "CXX=" + CXX + " "
            config_command = custom_config_command
            if "--cc=" in config_command:
                config_command = config_command.replace("--cc=clang-7", "--cc=" + CC)
            # print(config_command)

    elif os.path.exists(project_path + "/autogen.sh"):
        config_command = "./autogen.sh;"
        config_command += "CC=" + CC + " "
        config_command += "CXX=" + CXX + " "
        config_command += "./configure "
        config_command += "CFLAGS=\"" + C_FLAGS + "\" "
        config_command += "CXXFLAGS=\"" + CXX_FLAGS + "\""

    elif os.path.exists(project_path + "/configure.ac"):
        config_command = "autoreconf -i;"
        config_command += "CC=" + CC + " "
        config_command += "CXX=" + CXX + " "
        config_command += "./configure "
        config_command += "CFLAGS=\"" + C_FLAGS + "\" "
        config_command += "CXXFLAGS=\"" + CXX_FLAGS + "\""

    elif os.path.exists(project_path + "/configure.in"):
        config_command = "autoreconf -i;"
        config_command += "CC=" + CC + " "
        config_command += "CXX=" + CXX + " "
        config_command += "./configure "
        config_command += "CFLAGS=\"" + C_FLAGS + "\" "
        config_command += "CXXFLAGS=\"" + CXX_FLAGS + "\""

    elif os.path.exists(project_path + "/configure"):
        config_command = "CC=" + CC + " "
        config_command += "CXX=" + CXX + " "
        config_command += "./configure "
        config_command += "CFLAGS=\"" + C_FLAGS + "\" "
        config_command += "CXXFLAGS=\"" + CXX_FLAGS + "\""

    elif os.path.exists(project_path + "/CMakeLists.txt"):
        config_command = "cmake -DCMAKE_C_COMPILER=" + CC + " "
        config_command += "-DCMAKE_CPP_COMPILER=" + CXX + " "
        config_command += "-DCMAKE_C_FLAGS=\"" + C_FLAGS + "\" "
        config_command += "-DCMAKE_CXX_FLAGS=\"" + CXX_FLAGS + "\" . "

    if is_llvm:
        config_command = "LLVM_COMPILER=clang;" + config_command

    if not config_command:
        error_exit("[Not Found] Configuration Command")

    config_command = dir_command + config_command
    ret_code = execute_command(config_command)
    if int(ret_code) != 0:
        emitter.error(config_command)
        error_exit("CONFIGURATION FAILED!!\nExit Code: " + str(ret_code))


def apply_flags(build_command):
    if values.CONF_BUILD_FLAGS == "disable":
        return build_command
    c_flags = C_FLAGS
    ld_flags = LD_FLAGS
    if "XCFLAGS=" in build_command:
        c_flags_old = (build_command.split("XCFLAGS='")[1]).split("'")[0]
        if "-fPIC" in c_flags_old:
            c_flags = c_flags.replace("-static", "")
        c_flags_new = c_flags.replace("'", "") + " " + c_flags_old
        build_command = build_command.replace(c_flags_old, c_flags_new)
    elif "CFLAGS=" in build_command:
        c_flags_old = (build_command.split("CFLAGS='")[1]).split("'")[0]
        if "-fPIC" in c_flags_old:
            c_flags = c_flags.replace("-static", "")
        c_flags_new = c_flags.replace("'", "") + " " + c_flags_old
        build_command = build_command.replace(c_flags_old, c_flags_new)
    else:
        new_command = "make CFLAGS=\"" + c_flags + "\" "
        build_command = build_command.replace("make ", new_command)

    if "LDFLAGS=" in build_command:
        ld_flags_old = (build_command.split("LDFLAGS='")[1]).split("'")[0]
        ld_flags_new = ld_flags.replace("'", "") + " " + ld_flags_old
        build_command = build_command.replace(ld_flags_old, ld_flags_new)
    else:
        new_command = "make LDFLAGS=\"" + ld_flags + "\" "
        build_command = build_command.replace("make ", new_command)

    if "XCXXFLAGS=" in build_command:
        c_flags_old = (build_command.split("XCXXFLAGS='")[1]).split("'")[0]
        if "-fPIC" in c_flags_old:
            c_flags = c_flags.replace("-static", "")
        c_flags_new = c_flags.replace("'", "") + " " + c_flags_old
        build_command = build_command.replace(c_flags_old, c_flags_new)
    elif "CXXFLAGS=" in build_command:
        c_flags_old = (build_command.split("CXXFLAGS='")[1]).split("'")[0]
        if "-fPIC" in c_flags_old:
            c_flags = c_flags.replace("-static", "")
        c_flags_new = c_flags.replace("'", "") + " " + c_flags_old
        build_command = build_command.replace(c_flags_old, c_flags_new)
    else:
        new_command = "make CXXFLAGS=\"" + c_flags + "\" "
        build_command = build_command.replace("make ", new_command)

    if "XCC=" in build_command:
        cc_old = (build_command.split("XCC='")[1]).split("'")[0]
        build_command = build_command.replace(cc_old, CC)
    elif "CC=" in build_command:
        cc_old = (build_command.split("CC='")[1]).split("'")[0]
        build_command = build_command.replace(cc_old, CC)
    else:
        new_command = "make CC=" + CC + " "
        build_command = build_command.replace("make", new_command)

    if "XCXX=" in build_command:
        cc_old = (build_command.split("XCXX='")[1]).split("'")[0]
        build_command = build_command.replace(cc_old, CXX)
    elif "CXX=" in build_command:
        cc_old = (build_command.split("CXX='")[1]).split("'")[0]
        build_command = build_command.replace(cc_old, CXX)
    else:
        new_command = "make CXX=" + CXX + " "
        build_command = build_command.replace("make", new_command)

    return build_command


def build_project(project_path, build_command=None):
    emitter.sub_sub_title("building program")
    dir_command = "cd " + project_path + ";"
    if build_command is None:
        build_command = "CC=" + CC + " CXX=" + CXX + " "
        if values.CONF_BUILD_FLAGS == "disable":
            build_command += "bear make -j`nproc`  "
        else:
            build_command += "bear make CFLAGS=\"" + C_FLAGS + "\" "
            build_command += "CXXFLAGS=\"" + CXX_FLAGS + " LDFLAGS=" + LD_FLAGS + "\" -j`nproc` > "
    else:
        if not os.path.isfile(project_path + "/compile_commands.json"):
            build_command = build_command.replace("make ", "bear make ")
        if CC == "wllvm":
            build_command = remove_fsanitize(build_command)
        build_command = apply_flags(build_command)
    if not build_command:
        error_exit("[Not Found] Build Command")
    build_command = dir_command + build_command
    build_command = build_command + " > " + definitions.FILE_MAKE_LOG
    ret_code = execute_command(build_command)
    if int(ret_code) != 0:
        emitter.error(build_command)
        error_exit("BUILD FAILED!!\nExit Code: " + str(ret_code))


def build_normal():
    global CC, CXX, CXX_FLAGS, C_FLAGS, LD_FLAGS

    emitter.sub_title("Building Program")
    execute_command("export TRIDENT_CC=" + definitions.DIRECTORY_TOOLS + "/trident-cc")
    execute_command("export TRIDENT_CXX=" + definitions.DIRECTORY_TOOLS + "/trident-cxx")
    clean_project(values.CONF_DIR_SRC, values.CONF_PATH_PROGRAM)
    CC = "$TRIDENT_CC"
    CXX = "$TRIDENT_CXX"
    C_FLAGS = "-g -O0"
    CXX_FLAGS = "-g -O0"
    config_project(values.CONF_DIR_SRC, False, values.CONF_COMMAND_CONFIG)
    C_FLAGS = "-g -I /concolic-repair/runtime -L/concolic-repair/runtime -ltrident_runtime -lkleeRuntest"
    LDFLAGS = "-L/concolic-repair/lib -ltrident_runtime -ltrident_proxy -lkleeRuntest"
    CXX_FLAGS = C_FLAGS
    if values.CONF_STATIC:
        C_FLAGS += " -static"
        CXX_FLAGS += " -static"
    build_project(values.CONF_DIR_SRC, values.CONF_COMMAND_BUILD)


def remove_fsanitize(build_command):
    logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    sanitize_group = ['integer', 'address', 'undefined']
    for group in sanitize_group:
        build_command = str(build_command).replace("-fsanitize=" + str(group), "")
    return build_command


# def build_instrumented_code(source_directory):
#     logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
#     emitter.normal("\t\t\tbuilding instrumented code")
#     execute_command("export LLVM_COMPILER=clang")
#     global CXX_FLAGS, C_FLAGS, CC, CXX
#     CC = "wllvm"
#     CXX = "wllvm++"
#     CXX_FLAGS = "'-g -O0 -static -DNDEBUG '"
#     C_FLAGS = "'-g -O0 -static  -L/klee/build/lib -lkleeRuntest'"
#     LD_FLAGS = "'-L/klee/build/lib -lkleeRuntest'"
#
#     if os.path.exists(source_directory + "/" + "aclocal.m4"):
#         pre_config_command = "cd " + source_directory + ";"
#         pre_config_command += "rm aclocal.m4;aclocal"
#         execute_command(pre_config_command)
#
#     elif os.path.exists(source_directory + "/autogen.sh"):
#         pre_config_command = "./autogen.sh"
#         execute_command(pre_config_command)
#
#     if os.path.exists(source_directory + "/" + "CMakeCache.txt"):
#         config_command = "cd " + source_directory + ";"
#         config_command += "cmake -DCMAKE_EXE_LINKER_FLAGS=" + LD_FLAGS + " ."
#         execute_command(config_command)
#
#     build_command = "cd " + source_directory + ";"
#     custom_build_command = ""
#     if (values.PATH_A in source_directory) or (values.PATH_B in source_directory):
#         if values.BUILD_COMMAND_A is not None:
#             custom_build_command = values.BUILD_COMMAND_A
#
#     if values.PATH_C in source_directory:
#         if values.BUILD_COMMAND_C is not None:
#             custom_build_command = values.BUILD_COMMAND_C
#
#     # print("custom command is " + custom_build_command)
#
#     if not custom_build_command:
#         build_command += "make CFLAGS=" + C_FLAGS + " "
#         build_command += "CXXFLAGS=" + CXX_FLAGS + " > " + definitions.FILE_MAKE_LOG
#     else:
#         if not os.path.isfile(source_directory + "/compile_commands.json"):
#             custom_build_command = custom_build_command.replace("make", "bear make")
#         build_command = remove_fsanitize(build_command)
#         build_command_with_flags = apply_flags(custom_build_command)
#         build_command += build_command_with_flags
#
#     # print(build_command)
#     ret_code = execute_command(build_command)
#     if int(ret_code) == 2:
#         # TODO: check only upto common directory
#         while source_directory != "" and ret_code != "0":
#             build_command = build_command.replace(source_directory, "???")
#             source_directory = "/".join(source_directory.split("/")[:-1])
#             build_command = build_command.replace("???", source_directory)
#             ret_code = execute_command(build_command)
#
#     if int(ret_code) != 0:
#         emitter.error(build_command)
#         error_exit("BUILD FAILED!!\nExit Code: " + str(ret_code))


def build_verify(project_path):
    global CC, CXX, CXX_FLAGS, C_FLAGS, LD_FLAGS
    emitter.sub_sub_title("building projects")
    CC = "clang-7"
    CXX = "clang++-7"
    CXX_FLAGS = "'-g -O0 -static -DNDEBUG'"
    C_FLAGS = "'-g -O0 -static -DNDEBUG'"
    emitter.normal("\t\t" + project_path)
    clean_project(project_path)

    if values.CONF_COMMAND_CONFIGURATATION:
        config_project(project_path, False, values.CONF_COMMAND_CONFIGURATATION)
    else:
        config_project(project_path, False)

    if values.CONF_COMMAND_BUILD:
        CXX_FLAGS = "'-g -O0 -static -DNDEBUG -fsanitize=" + values.CONF_FLAG_ASAN + "'"
        C_FLAGS = "'-g -O0 -static -DNDEBUG -fsanitize=" + values.CONF_FLAG_ASAN + "'"
        build_project(project_path, values.CONF_COMMAND_BUILD)
    else:
        CXX_FLAGS = "'-g -O0 -static -DNDEBUG -fsanitize=" + values.CONF_FLAG_ASAN + "'"
        C_FLAGS = "'-g -O0 -static -DNDEBUG -fsanitize=" + values.CONF_FLAG_ASAN + "'"
        build_project(project_path)


def build_asan(project_path):
    global CC, CXX, CXX_FLAGS, C_FLAGS, LD_FLAGS
    clean_project(project_path)
    CC = "clang-7"
    CXX = "clang++-7"
    CXX_FLAGS = "'-g -O0 -static'"
    C_FLAGS = "'-g -O0 -static'"
    config_project(project_path)
    CXX_FLAGS = "'-g -O0 -static -DNDEBUG -fsanitize=" + values.ASAN_FLAG + "'"
    C_FLAGS = "'-g -O0 -static -DNDEBUG -fsanitize=" + values.ASAN_FLAG + "'"
    build_project(project_path)


def build_llvm(project_path):
    global CC, CXX, CXX_FLAGS, C_FLAGS, LD_FLAGS
    clean_project(project_path)
    os.environ["LLVM_COMPILER"] = "clang"
    CC = "wllvm"
    CXX = "wllvm++"
    CXX_FLAGS = "'-g -O0 -static'"
    C_FLAGS = "'-g -O0 -static'"
    config_project(project_path)
    CXX_FLAGS = "'-g -O0 -static -DNDEBUG '"
    C_FLAGS = "'-g -O0 -static  -L/klee/build/lib -lkleeRuntest'"
    build_project(project_path)


def restore_project(project_path):
    restore_command = "cd " + project_path + ";"
    if os.path.exists(project_path + "/.git"):
        restore_command += "git clean -fd; git reset --hard HEAD"
    elif os.path.exists(project_path + "/.svn"):
        restore_command += "svn revert -R .; svn status --no-ignore | grep '^\?' | sed 's/^\?     //'  | xargs rm -rf"
    elif os.path.exists(project_path + "/.hg"):
        restore_command += "hg update --clean; hg st -un0 | xargs -0 rm"
    else:
        return
    # print(restore_command)
    execute_command(restore_command)


def soft_restore_project(project_path):
    restore_command = "cd " + project_path + ";"
    if os.path.exists(project_path + "/.git"):
        restore_command += "git reset --hard HEAD"
    elif os.path.exists(project_path + "/.svn"):
        restore_command += "svn revert -R .; "
    elif os.path.exists(project_path + "/.hg"):
        restore_command += "hg update --clean"
    else:
        return
    # print(restore_command)
    execute_command(restore_command)


def clean_project(project_path, binary_path):
    emitter.sub_sub_title("cleaning files")
    binary_dir_path = "/".join(str(binary_path).split("/")[:-1])
    clean_command = "cd " + project_path + "; make clean"
    clean_command += "; rm compile_commands.json"
    clean_command += "; rm CMakeCache.txt"
    clean_command += "; rm -rf CMakeFiles"
    execute_command(clean_command)
    clean_residues = "cd " + binary_dir_path + ";" + "rm -rf ./patches/*;" + "rm -rf ./klee*"
    execute_command(clean_residues)
