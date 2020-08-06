import subprocess
import os
import sys
from pysmt.smtlib.parser import SmtLibParser
from pysmt.shortcuts import write_smtlib


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


def z3_get_model(formula):
    path_script = "/tmp/z3_script"
    path_result = "/tmp/z3_output"
    write_smtlib(formula, path_script)
    with open(path_script, "a") as script_file:
        script_file.writelines(["(get-model)\n", "(exit)\n"])
    z3_command = "z3 " + path_script + " > " + path_result
    process = subprocess.Popen([z3_command], stderr=subprocess.PIPE, shell=True)
    (output, error) = process.communicate()
    with open(path_result, "r") as result_file:
        z3_output = result_file.readlines()
    print(z3_output)
    model_byte_list = parse_z3_output(z3_output)
    print(model_byte_list)

def parse_z3_output(z3_output):
    model = dict()
    collect_lambda = False
    var_name = ""
    byte_list = dict()
    str_lambda = ""
    for line in z3_output:
        if "define-fun " in line:
            var_name = line.split("define-fun ")[1].split(" ()")[0]
            collect_lambda = False
        if collect_lambda:
            str_lambda += line
        if "lambda " in line or "as const " in line:
            collect_lambda = True
            str_lambda = line

        if (not collect_lambda and str_lambda) or (line == z3_output[-1]):
            if "const" in str_lambda:
                str_value = str_lambda.split("#x")[-1].split(")")[0]
                byte_list = dict()
                byte_list[0] = int("0x" + str_value, 16)
            elif "ite" in str_lambda:
                max_index = 0
                byte_list = dict()
                token_list = str_lambda.split("(ite (= x!1 ")
                for token in token_list[1:]:
                    if token.count("#x") == 2:
                        index, value = token.split(") ")
                    elif token.count("#x") == 3:
                        index, value, default = token.split(" ")
                        index = index.replace(")", "")
                        default = default.split(")")[0].replace("#", "0")
                    index = index.replace("#", "0")
                    value = value.replace("#", "0")
                    index = int(index, 16)
                    if index > max_index:
                        max_index = index
                    byte_list[index] = int(value, 16)
                for i in range(0, max_index):
                    if i not in byte_list:
                        byte_list[i] = int(default, 16)

            else:
                print("Unhandled output")
                print(str_lambda)
                print(z3_output)
                exit(1)

        if var_name and byte_list:
            model[var_name] = byte_list
            var_name = ""
            byte_list = dict()


    return model

