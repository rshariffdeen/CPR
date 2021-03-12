import subprocess
import os
import sys
sys.path.append('/CPR/app')
from concolic import run_concolic_exploration

## compile the test.c
compile_command = "export LLVM_COMPILER=clang;" \
                  "wllvm -l kleeRuntest -g -O0 -o test test.c;" \
                  "extract-bc test"

process = subprocess.Popen([compile_command], stderr=subprocess.PIPE, shell=True)
(output, error) = process.communicate()
assert int(process.returncode) == 0

second_var_list = [{"identifier": "k", "value": 50, "size": 4}]
argument_list = [5, 28]
run_concolic_exploration("test.bc", argument_list, second_var_list, "/CPR/tests/concolic")


