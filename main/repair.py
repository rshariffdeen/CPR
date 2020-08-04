import os
import synthesis as trident
from concolic import run_concolic_exploration, run_concolic_execution, generate_new_input
import subprocess
import sys


def init (working_path):
   os.chdir(working_path)
   os.system("rm -rf ./patches/*")

   #sys.path.append('/concolic-repair/main')

   ## Build the program under test.
   os.system("./build")
   # compile_command = "export LLVM_COMPILER=clang;" \
   #                   "wllvm -l kleeRuntest -o -g -O0 test test.c;" \
   #                   "extract-bc test"
   # process = subprocess.Popen([compile_command], stderr=subprocess.PIPE, shell=True)
   # (output, error) = process.communicate()
   # assert int(process.returncode) == 0

   ## Execute klee with this program so to generate the expected results for test cases.
   # klee --posix-runtime --libc=uclibc --write-smt2s --output-dir=klee-t1 "${PROGRAM}.bc" 1
   os.system("klee --posix-runtime --libc=uclibc --write-smt2s --output-dir=klee-t1 'test.bc' 1")


def reduce(): # TODO
   # Reduces the set of patch candidates based on the current path constraint
   # Iterate over patches and check if they still hold based on path constraint.
   check()
   return False


def check(): # TODO
   # checks, e.g., for crash freedom
   return True


def checkCoverage(): # TODO
   return True # Only for testing purpose. 


def main():

   project_path = "/concolic-repair/tests/example/"
   
   # Prepare the program under test.
   init(project_path)

   ## Generate all possible solutions by running the synthesizer.
   # trident.main(["--tests", "t1.smt2:klee-t1", "--components", "components/*.smt2", "../../components/less-than.smt2", "../../components/constant_a.smt2", "--all", "--output", "patches"])
   trident.main(["--tests", "t1.smt2:klee-t1", "--components", "components/x.smt2", "../../components/less-than.smt2", "../../components/constant_a.smt2", "--all", "--output", "patches"])

   numberOfPatches = len(os.listdir("./patches"))
   print("|P|=" + str(numberOfPatches))

   # Log file for the previous concolic execution that captures PPC.
   log_path = "" # TODO how do we init the log_path?

   satisfied = numberOfPatches <= 1
   while not satisfied:

      # Pick new input and patch candidate for next concolic execution step.
      # input_arg_list, input_var_list = generate_new_input(log_path, project_path) #TODO patch candidate missing

      # Concolic execution of concrete input and patch candidate to retrieve path constraint.
      second_var_list = [{"identifier": "x", "value": 1, "size": 4}]
      argument_list = [1]
      status = run_concolic_execution("test.bc", argument_list, second_var_list, print_output=True)
      print(status)

      # 

      
      satisfied = checkCoverage()



   print("Finished.")


if __name__ == "__main__":
    main()