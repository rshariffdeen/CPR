from main.concolic import run_concolic_execution, generate_new_input
from main.synthesis import load_specification, synthesize, Program
from pathlib import Path
from typing import List, Dict, Tuple
from main import emitter, values, distance, oracle, parallel, definitions, writer, reader
import time


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
        test_index = str((int(test_output_list.index(output_spec)) * 2) + 1)
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
    writer.write_as_pickle(list_of_patches, definitions.FILE_PATCH_SET)
    emitter.normal("\tnumber of patches in pool: " + str(len(list_of_patches)))
    return list_of_patches
