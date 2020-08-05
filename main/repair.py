import subprocess
import os
import sys
sys.path.append('/concolic-repair/main')
from concolic import generate_ktest, run_concolic_execution, run_concrete_execution, generate_new_input
from utilities import build_program
import synthesis as trident

def init (cwd, program_name):
   os.chdir(cwd)
   os.system("rm -rf ./patches/*")
   os.system("rm -rf ./klee*")

   program_path = cwd + "/" + program_name

   ## Build the program under test.
   build_status = build_program(program_path)
   assert int(build_status) == 0
   assert os.path.isfile(program_path)
   assert os.path.getsize(program_path) > 0

   ## Execute klee with this program so to generate the expected results for test cases.
   argument_list = [1]
   ktest_path, exit_code = generate_ktest(argument_list, {})
   assert int(exit_code) == 0
   assert os.path.isfile(ktest_path)
   assert os.path.getsize(ktest_path) > 0
   exit_code = run_concrete_execution(program_name + ".bc", argument_list, {}, True)
   assert exit_code == 0
   klee_file_1 = cwd + "/klee-out-0/test000001.smt2"
   assert os.path.isfile(klee_file_1)
   assert os.path.getsize(klee_file_1) > 0


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

   project_path = "/concolic-repair/tests/example"
   program = "test"

   # Prepare the program under test.
   init(project_path, program)

   ## Generate all possible solutions by running the synthesizer.
   synthesis_arguments = [
      "--tests", "t1.smt2:klee-out-0",
      "--components", "components/x.smt2", "../../components/less-than.smt2", "../../components/constant_a.smt2",
      "--all-values", " -10:11",
      "--output", "patches"
      ]
   trident.main(synthesis_arguments)

   numberOfPatches = len(os.listdir("./patches"))
   print("|P|=" + str(numberOfPatches))

   # TODO this is a dummy call to produce the first results
   global list_path_explored, list_path_detected
   second_var_list = [{"identifier": "x", "value": 1, "size": 4}]
   argument_list = [1]
   run_concolic_execution(program + ".bc", argument_list, second_var_list, True)
   ppc_log_path = project_path + "/klee-last/ppc.log"
   print(">> " + str(ppc_log_path))

   print(">> start repair loop")

   satisfied = numberOfPatches <= 1
   while not satisfied:

      # Pick new input and patch candidate for next concolic execution step.
      gen_arg_list, gen_var_list = generate_new_input(ppc_log_path, project_path) #TODO (later) patch candidate missing

      # Concolic execution of concrete input and patch candidate to retrieve path constraint.
      status = run_concolic_execution(program + ".bc", gen_arg_list, gen_var_list)
      print(status)

      # Reduces the set of patch candidates based on the current path constraint
      reduce()

      # Checks for the current coverage.
      satisfied = checkCoverage()


   print("Finished.")


if __name__ == "__main__":
    main()






