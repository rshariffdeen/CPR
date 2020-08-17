import subprocess
import os
import sys
import random
sys.path.append('/concolic-repair/main')
from concolic import generate_ktest, run_concolic_execution, run_concrete_execution, generate_new_input
from utilities import build_program
from synthesis import load_components, load_specification, synthesize, Program, program_to_formula, collect_symbols, RuntimeSymbol, ComponentSymbol
from pathlib import Path
from typing import List, Dict, Tuple
from main import emitter, definitions, values

check_counter = 0


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
   emitter.sub_title("Generating Patch Pool")

   gen_comp_files = []
   os.chdir(definitions.DIRECTORY_COMPONENTS)
   gen_comp_files.append(Path("less-than.smt2"))
   gen_comp_files.append(Path("constant_a.smt2"))
   general_components = load_components(gen_comp_files)

   proj_comp_files = []
   os.chdir(project_path)
   proj_comp_files.append(Path("components/x.smt2"))
   project_components = load_components(proj_comp_files)

   components = project_components + general_components
   depth = 3

   spec_files = []
   spec_files.append((Path("t1.smt2"), Path("klee-out-0")))
   specification = load_specification(spec_files)

   concrete_enumeration = True
   lower_bound = -10
   upper_bound = 11

   result = synthesize(components, depth, specification, concrete_enumeration, lower_bound, upper_bound)

   list_of_patches = [_ for _ in result]
   emitter.normal("\tnumber of patches in pool: " + str(len(list_of_patches)))
   return list_of_patches


def run(project_path, program_name):
   emitter.title("Repairing Program")
   program_path = project_path + "/" + program_name
   ## Generate all possible solutions by running the synthesizer.
   P = generate_patch_set(project_path)
   ppc_log_path = project_path + "/klee-last/ppc.log"
   expr_log_path = project_path + "/klee-last/expr.log"

   emitter.sub_title("Evaluating Patch Pool")
   satisfied = len(P) <= 1
   while not satisfied and len(P) > 1:

      ## Pick new input and patch candidate for next concolic execution step.
      random_patch_selection = random.choice(P)
      lid = list(random_patch_selection.keys())[0]
      eid = 0
      patch_component = random_patch_selection[lid]
      patch_constraint = program_to_formula(patch_component)

      program_substitution = {}
      for program_symbol in collect_symbols(patch_constraint, lambda x: True):
         kind = ComponentSymbol.check(program_symbol)
         data = ComponentSymbol.parse(program_symbol)._replace(lid=lid)._replace(eid=eid)
         if kind == ComponentSymbol.RRETURN:
            program_substitution[program_symbol] = RuntimeSymbol.angelic(data)
         elif kind == ComponentSymbol.RVALUE:
            program_substitution[program_symbol] = RuntimeSymbol.rvalue(data)
         elif kind == ComponentSymbol.LVALUE:
            program_substitution[program_symbol] = RuntimeSymbol.lvalue(data)
         else:
            pass  # FIXME: do I need to handle it somehow?
      substituted_patch = patch_constraint.substitute(program_substitution)
      argument_list = values.ARGUMENT_LIST
      second_var_list = values.SECOND_VAR_LIST
      gen_arg_list, gen_var_list = generate_new_input(ppc_log_path, expr_log_path, project_path, argument_list, second_var_list, substituted_patch) #TODO (later) patch candidate missing
      assert gen_arg_list # there should be a concrete input
      print(">> new input: " + str(gen_arg_list)) 

      ## Concolic execution of concrete input and patch candidate to retrieve path constraint.
      exit_code = run_concolic_execution(program_path + ".bc", gen_arg_list, gen_var_list)
      assert exit_code == 0

      ## Reduces the set of patch candidates based on the current path constraint
      P = reduce(P, project_path + "/klee-last/", gen_arg_list, assertion)
      print("|P|=" + str(len(P)))

      # Checks for the current coverage.
      satisfied = checkCoverage()





