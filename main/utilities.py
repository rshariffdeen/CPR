import subprocess
import os
import sys


def build_clean(program_path):
    clean_command = "cd " + program_path + "; make clean; rm -rf klee-*"
    process = subprocess.Popen([clean_command], stderr=subprocess.PIPE, shell=True)
    (output, error) = process.communicate()
    assert int(process.returncode) == 0
    return int(process.returncode)


def build_program(program_path):
    program_name = program_path.split("/")[-1]
    if os.path.isfile(program_path):
        build_clean(program_path)
    program_loc = "/".join(program_path.split("/")[:-1])
    compile_command = "cd " + program_loc + ";"
    compile_command += "export TRIDENT_CC=/concolic-repair/main/trident-cc;" \
                      "CC=\"$TRIDENT_CC\" make -e;" \
                      "extract-bc " + program_name
    process = subprocess.Popen([compile_command], stderr=subprocess.PIPE, shell=True)
    (output, error) = process.communicate()
    return int(process.returncode)


def z3_get_model(str_formula):
    str_formula = str_formula.replace("(exit)", "(get-model)\n(exit)")
    path_script = "/tmp/z3_script"
    with open(path_script, "w") as script_file:
        script_file.writelines(str_formula)
    z3_command = "z3 " + path_script
    process = subprocess.Popen([z3_command], stderr=subprocess.PIPE, shell=True)
    (output, error) = process.communicate()
    print(output)

