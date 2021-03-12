import subprocess
import os
import sys
sys.path.append('/CPR/app')
from concolic import generate_ktest, run_concolic_execution


## compile the test.c
compile_command = "export LLVM_COMPILER=clang;" \
                  "wllvm -l kleeRuntest -o test test.c;" \
                  "extract-bc test"

process = subprocess.Popen([compile_command], stderr=subprocess.PIPE, shell=True)
(output, error) = process.communicate()
assert int(process.returncode) == 0

second_var_list = [{"identifier": "k", "value": 50, "size": 4}]
argument_list = [5, 28]
ktest_path, exit_code = generate_ktest(argument_list, second_var_list)

assert int(exit_code) == 0
assert os.path.isfile(ktest_path)
assert os.path.getsize(ktest_path) > 0

verify_command = "ktest-tool " + ktest_path
process = subprocess.Popen([verify_command], stderr=subprocess.PIPE, shell=True)
(output, error) = process.communicate()
assert int(process.returncode) == 0
print(output)


exit_code = run_concolic_execution("test.bc", argument_list, second_var_list, True)
assert exit_code == 0
verify_command = "cat klee-last/test000001.smt2"
process = subprocess.Popen([verify_command], stderr=subprocess.PIPE, shell=True)
(output, error) = process.communicate()

