import subprocess
import os
import sys
sys.path.append('/concolic-repair/main')
from concolic import generate_ktest, run_concolic_execution
from utilities import build_program


program_name = "test"
cwd = os.path.dirname(os.path.realpath(__file__))
program_path = cwd + "/" + program_name

build_status = build_program(program_path)
assert int(build_status) == 0
assert os.path.isfile(program_path)
assert os.path.getsize(program_path) > 0


second_var_list = []
argument_list = [0]
ktest_path, exit_code = generate_ktest(argument_list, second_var_list)
assert int(exit_code) == 0
assert os.path.isfile(ktest_path)
assert os.path.getsize(ktest_path) > 0
exit_code = run_concolic_execution(program_name + ".bc", argument_list, second_var_list, True)
assert exit_code == 0
klee_file_1 = cwd + "/klee-out-0/test000001.smt2"
assert os.path.isfile(klee_file_1)
assert os.path.getsize(klee_file_1) > 0



second_var_list = []
argument_list = [1]
ktest_path, exit_code = generate_ktest(argument_list, second_var_list)
assert int(exit_code) == 0
assert os.path.isfile(ktest_path)
assert os.path.getsize(ktest_path) > 0
exit_code = run_concolic_execution(program_name + ".bc", argument_list, second_var_list, True)
assert exit_code == 0
klee_file_2 = cwd + "/klee-out-1/test000001.smt2"
assert os.path.isfile(klee_file_2)
assert os.path.getsize(klee_file_2) > 0

synthesis_command = "python3.6 ../../main/synthesis.py \
          --tests t1.smt2:klee-out-0 t2.smt2:klee-out-1 \
          --components components/*.smt2 ../../components/assignment.smt2 ../../components/addition.smt2 ../../components/constant_a.smt2 \
          --all"

process = subprocess.Popen([synthesis_command], stderr=subprocess.PIPE, shell=True)
(output, error) = process.communicate()
assert int(process.returncode) == 0
