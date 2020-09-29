from main.synthesis import load_specification, synthesize, Program
from pathlib import Path
from typing import List, Dict, Tuple
from main import emitter, values, distance, oracle, parallel, definitions, writer, reader
from main import definitions, values, emitter
from pysmt.shortcuts import is_sat, Not, And, is_unsat
from pysmt.smtlib.parser import SmtLibParser
from six.moves import cStringIO



def generate_patch_set(project_path) -> List[Dict[str, Program]]:

    definitions.FILE_PATCH_SET = definitions.DIRECTORY_OUTPUT + "/patch-set"

    if values.CONF_SKIP_GEN:
        emitter.sub_title("Loading Patch Pool")
        list_of_patches = reader.read_pickle(definitions.FILE_PATCH_SET)
        emitter.normal("\tnumber of patches in pool: " + str(len(list_of_patches)))
        return list_of_patches

    emitter.sub_title("Generating Patch Pool")
    test_output_list = values.CONF_TEST_OUTPUT
    components = values.LIST_COMPONENTS
    depth = values.DEFAULT_DEPTH
    if values.CONF_DEPTH_VALUE.isnumeric():
        depth = int(values.CONF_DEPTH_VALUE)

    spec_files = []
    binary_dir_path = "/".join(values.CONF_PATH_PROGRAM.split("/")[:-1])
    for output_spec in test_output_list:
        output_spec_path = Path(project_path + "/" + output_spec)
        test_index = str((int(test_output_list.index(output_spec)) * 2) )
        klee_spec_path = Path(binary_dir_path + "/klee-out-" + test_index)
        spec_files.append((output_spec_path, klee_spec_path))
    specification = load_specification(spec_files)
    values.TEST_SPECIFICATION = specification
    concrete_enumeration = False
    if values.CONF_PATCH_TYPE == values.OPTIONS_PATCH_TYPE[0]:
        concrete_enumeration = True
    lower_bound = values.DEFAULT_LOWER_BOUND
    upper_bound = values.DEFAULT_UPPER_BOUND

    result = synthesize(components, depth, specification, concrete_enumeration, lower_bound, upper_bound)

    list_of_patches = [_ for _ in result]
    # writer.write_as_pickle(list_of_patches, definitions.FILE_PATCH_SET)
    emitter.normal("\tnumber of patches in pool: " + str(len(list_of_patches)))
    return list_of_patches


def generate_flipped_path(ppc):
    """
    This function will check if a selected path is feasible
           ppc : partial path conditoin at chosen control loc
           chosen_control_loc: branch location selected for flip
           returns satisfiability of the negated path
    """
    parser = SmtLibParser()
    script = parser.get_script(cStringIO(ppc))
    formula = script.get_last_formula()
    prefix = formula.arg(0)
    constraint = formula.arg(1)
    new_path = And(prefix, Not(constraint))

    assert str(new_path.serialize()) != str(formula.serialize())
    return new_path
