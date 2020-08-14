import subprocess
import os
import sys
import random
sys.path.append('/concolic-repair/main')
from concolic import generate_ktest, run_concolic_execution, run_concrete_execution, generate_new_input
from utilities import build_program
from synthesis import load_components, load_specification, synthesize, Program, program_to_formula
from pathlib import Path
from typing import List, Dict, Tuple

check_counter = 0

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


def reduce(current_patch_set: List[Dict[str, Program]], path_to_concolic_exec_result: str, concrete_input: [], assertion) -> List[Tuple[str, Program]]: # TODO
   # Reduces the set of patch candidates based on the current path constraint
   # Iterate over patches and check if they still hold based on path constraint.
   updated_patch_set = []
   for patch in current_patch_set:
      if check(patch, path_to_concolic_exec_result, concrete_input, assertion):
         updated_patch_set.append(patch)
   return current_patch_set 


def check(patch: Dict[str, Program], path_to_concolic_exec_result: str, concrete_input: [], assertion): # TODO
   # checks, e.g., for crash freedom
   return True


def checkCoverage(): # TODO
   global check_counter
   if check_counter < 10: # Only for testing purpose. 
      check_counter += 1
      return False
   else:   
      return True 


def generate_patch_set(project_path) -> List[Dict[str, Program]]:
   comp_files = []
   comp_files.append(Path("components/x.smt2"))
   comp_files.append(Path("../../components/less-than.smt2"))
   comp_files.append(Path("../../components/constant_a.smt2"))
   components = load_components(comp_files)

   depth = 3

   spec_files = []
   spec_files.append((Path("t1.smt2"), Path("klee-out-0")))
   specification = load_specification(spec_files)

   concrete_enumeration = True
   lower_bound = -10
   upper_bound = 11

   result = synthesize(components, depth, specification, concrete_enumeration, lower_bound, upper_bound)

   list_of_patches = [_ for _ in result]
   return list_of_patches


def main():

   project_path = "/concolic-repair/tests/example"
   program = "test"

   assertion = "path_to_assertion_file" # TODO

   ## Prepare the program under test.
   init(project_path, program)

   ## Generate all possible solutions by running the synthesizer.
   P = generate_patch_set(project_path)
   print("|P|=" + str(len(P)))

   ## This is a dummy call to produce the first results.
   global list_path_explored, list_path_detected
   second_var_list = [{"identifier": "x", "value": 1, "size": 4}]
   argument_list = [1]
   run_concolic_execution(program + ".bc", argument_list, second_var_list, True)
   ppc_log_path = project_path + "/klee-last/ppc.log"
   expr_log_path = project_path + "/klee-last/expr.log"

   print(">> start repair loop")

   satisfied = len(P) <= 1
   while not satisfied and len(P) > 1:

      ## Pick new input and patch candidate for next concolic execution step.
      random_patch = random.choice(P)
      patch_constraint = program_to_formula(random_patch)
      gen_arg_list, gen_var_list = generate_new_input(ppc_log_path, expr_log_path, project_path, argument_list, second_var_list, patch_constraint) #TODO (later) patch candidate missing
      assert gen_arg_list # there should be a concrete input
      print(">> new input: " + str(gen_arg_list)) 

      ## Concolic execution of concrete input and patch candidate to retrieve path constraint.
      exit_code = run_concolic_execution(program + ".bc", gen_arg_list, gen_var_list)
      assert exit_code == 0

      ## Reduces the set of patch candidates based on the current path constraint
      P = reduce(P, project_path + "/klee-last/", gen_arg_list, assertion)
      print("|P|=" + str(len(P)))

      # Checks for the current coverage.
      satisfied = checkCoverage()

   print("Finished.")


if __name__ == "__main__":
    main()






