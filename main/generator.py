from main.synthesis import load_specification, synthesize_parallel, Program
from pathlib import Path
from typing import List, Dict, Tuple
from six.moves import cStringIO
from pysmt.shortcuts import is_sat, Not, And, Or, TRUE, BVSGE, BVSLE, Int, NotEquals, SBV, Equals, BVConcat, Select, BV
import os
from pysmt.smtlib.parser import SmtLibParser
from pysmt.typing import BV32, BV8, ArrayType
from pysmt.shortcuts import write_smtlib, get_model, Symbol, is_sat, is_unsat, to_smtlib
from main.utilities import execute_command
from main import emitter, values, reader, parallel, definitions, extractor, oracle, utilities, parser
import re
import struct
import random
import copy

File_Log_Path = "/tmp/log_sym_path"
File_Ktest_Path = "/tmp/concolic.ktest"


def generate_patch(project_path, model_list=None) -> List[Dict[str, Program]]:

    definitions.FILE_PATCH_SET = definitions.DIRECTORY_OUTPUT + "/patch-set"

    emitter.sub_sub_title("Generating Patch")
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
    if model_list:
        for output_spec_path, klee_spec_path in model_list:
            spec_files.append((Path(output_spec_path), Path(klee_spec_path)))
    specification = load_specification(spec_files)
    values.TEST_SPECIFICATION = specification
    concrete_enumeration = False
    if values.CONF_PATCH_TYPE == values.OPTIONS_PATCH_TYPE[0]:
        concrete_enumeration = True
    lower_bound = values.DEFAULT_PATCH_LOWER_BOUND
    upper_bound = values.DEFAULT_PATCH_UPPER_BOUND + 1

    result = synthesize_parallel(components, depth, specification, concrete_enumeration, lower_bound, upper_bound)

    list_of_patches = [_ for _ in result]
    # writer.write_as_pickle(list_of_patches, definitions.FILE_PATCH_SET)
    emitter.normal("\tnumber of patches in pool: " + str(len(list_of_patches)))
    # filtered_list_of_patches = list(set(list_of_patches))
    # emitter.warning("\t[warning] found " + str(len(list_of_patches) - len(filtered_list_of_patches)) + "duplicate patch(es)")
    return list_of_patches[0]


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
    lower_bound = values.DEFAULT_PATCH_LOWER_BOUND
    upper_bound = values.DEFAULT_PATCH_UPPER_BOUND + 1

    result = synthesize_parallel(components, depth, specification, concrete_enumeration, lower_bound, upper_bound)

    list_of_patches = [_ for _ in result]
    # writer.write_as_pickle(list_of_patches, definitions.FILE_PATCH_SET)
    emitter.normal("\tnumber of patches in pool: " + str(len(list_of_patches)))
    # filtered_list_of_patches = list(set(list_of_patches))
    # emitter.warning("\t[warning] found " + str(len(list_of_patches) - len(filtered_list_of_patches)) + "duplicate patch(es)")
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


def generate_angelic_val_for_crash(klee_out_dir):
    file_list = [os.path.join(klee_out_dir, f) for f in os.listdir(klee_out_dir) if os.path.isfile(os.path.join(klee_out_dir,f))]
    error_file_path = None
    for file_name in file_list:
        if ".err" in file_name:
            error_file_path = file_name.split(".")[0] + ".smt2"
            break
    if error_file_path is None:
        error_file_path = klee_out_dir + "/test000001.smt2"
    sym_path = extractor.extract_formula_from_file(error_file_path)
    input_arg_list, input_var_list = generate_new_input(sym_path, values.ARGUMENT_LIST)
    return input_arg_list, input_var_list


def generate_mask_bytes(klee_out_dir):
    mask_byte_list = list()
    log_path = klee_out_dir + "/concrete.log"
    concretized_byte_list = reader.collect_concretized_bytes(log_path)
    smt2_file_path = klee_out_dir + "/test000001.smt2"
    control_byte_list = reader.collect_bytes_from_smt2(smt2_file_path)
    emitter.data("Control Byte List", control_byte_list)
    fixed_byte_list = list()
    if "A-data" in concretized_byte_list:
        influence_byte_list = sorted(list(concretized_byte_list["A-data"]))
        emitter.data("Influencing Byte List", influence_byte_list)
    fixed_byte_list = control_byte_list
    if values.CONF_PATH_POC:
        byte_length = os.path.getsize(values.CONF_PATH_POC)
        for i in range(0, byte_length):
            if i not in fixed_byte_list:
                mask_byte_list.append(i)
    return sorted(mask_byte_list)


def generate_model(formula):
    """
           This function will invoke PySMT APIs to solve the provided formula and return the byte list of the model
           Arguments:
               formula: smtlib formatted formula
    """
    emitter.debug("extracting z3 model")
    model = get_model(formula)
    if model is None:
        return None
    path_script = "/tmp/z3_script"
    write_smtlib(formula, path_script)
    with open(path_script, "r") as script_file:
        script_lines = script_file.readlines()
    script = "".join(script_lines)
    var_list = set(re.findall("\(declare-fun (.+?) \(\)", script))
    sym_var_list = dict()
    for var_name in var_list:
        # sym_var_list[var_name] = dict()
        if "const_" in var_name:
            sym_def = Symbol(var_name, BV32)
            if sym_def not in model:
                continue
            x = model[sym_def]
            byte_list = dict()
            default_value = x.bv_signed_value()
            byte_list[0] = default_value
        else:
            sym_def = Symbol(var_name, ArrayType(BV32, BV8))
            if sym_def not in model:
                continue
            x = model[sym_def].simplify()
            byte_list = dict()
            value_array_map = x.array_value_assigned_values_map()
            default_value = int(str(x.array_value_default()).split("_")[0])
            if not value_array_map:
                byte_list[0] = default_value
            else:
                for idx, val in value_array_map.items():
                    index = int(str(idx).split("_")[0])
                    value = int(str(val).split("_")[0])
                    byte_list[index] = value

                max_index = max(list(byte_list.keys()))
                if var_name in values.LIST_BIT_LENGTH:
                    array_size = values.LIST_BIT_LENGTH[var_name] - 1
                    if var_name in ["A-data"]:
                        array_size = max_index

                else:
                    array_size = max_index + 1  # TODO: this could be wrong calculation

                if max_index == 0:
                    array_size = 2

                if var_name not in ["A-data"]:
                    for i in range(0, array_size):
                        if i not in byte_list:
                            byte_list[i] = default_value

                if var_name not in ["A-data", "A-data-stat"]:
                    for i in range(array_size - 1, -1, -1):
                        if byte_list[i] == 0:
                            byte_list.pop(i)
                        else:
                            break
        sym_var_list[var_name] = byte_list
    emitter.data("model var list", sym_var_list)
    return sym_var_list


def generate_constant_value_list(sym_path):
    gen_const_list = dict()
    gen_var_list = dict()
    const_val_list = dict()
    model = generate_model(sym_path)
    if model is None:
        return None
    for var_name in model:
        var_byte_list = model[var_name]
        if "const" in var_name:
            gen_const_list[var_name] = var_byte_list
        else:
            gen_var_list[var_name] = var_byte_list

    for const_name in gen_const_list:
        bit_vector = gen_const_list[const_name]
        const_value = utilities.get_signed_value(bit_vector)
        print(const_name, const_value)
        const_val_list[const_name] = const_value

    emitter.data("Generated Constant List", const_val_list)
    return const_val_list


def generate_new_input(sym_path, argument_list):
    gen_arg_list = dict()
    gen_var_list = dict()
    input_var_list = list()
    input_arg_dict = dict()
    input_arg_list = list()
    model = generate_model(sym_path)
    if model is None:
        return None, None
    for var_name in model:
        var_byte_list = model[var_name]
        if "arg" in var_name:
            gen_arg_list[var_name] = var_byte_list
        else:
            gen_var_list[var_name] = var_byte_list

    for arg_name in gen_arg_list:
        bit_vector = gen_arg_list[arg_name]
        arg_index = int(str(arg_name).replace("arg", ""))
        arg_str = utilities.get_str_value(bit_vector)
        arg_value = utilities.get_signed_value(bit_vector) - 48
        # print(arg_name, arg_index, arg_value)
        if str(argument_list[arg_index]).isnumeric():
            input_arg_dict[arg_index] = str(arg_value)
            # emitter.debug(arg_name, arg_value)
        else:
            input_arg_dict[arg_index] = arg_str
            # emitter.debug(arg_name, arg_str)

    # fill random values if not generated
    offset = 0
    for arg in argument_list:
        index = list(argument_list).index(arg) - offset
        if "$POC" in arg:
            input_arg_list.append(str(argument_list[index]))
            offset = 1
        elif str(index) in values.CONF_MASK_ARG:
            input_arg_list.append(arg)
        elif index in input_arg_dict:
            input_arg_list.append(input_arg_dict[index])
        else:
            arg_len = len(str(argument_list[index]))
            random_value = ""
            for j in range(0, arg_len):
                random_value += chr(random.randint(0, 128))
            input_arg_list.append(random_value)

    for var_name in gen_var_list:
        bit_vector = gen_var_list[var_name]
        var_value = 0
        var_size = len(bit_vector)
        if var_name in ["A-data", "A-data-stat"]:
            if var_name == "A-data":
                generate_binary_file(bit_vector)
            continue
        if bit_vector:
            var_value = utilities.get_signed_value(bit_vector)
        # emitter.debug(var_name, var_value)
        if "angelic" in var_name:
            input_var_list.append({"identifier": var_name, "value": var_value, "size": 4})

    # for var_tuple in second_var_list:
    #     var_name = var_tuple['identifier']
    #     if var_name not in gen_var_list:
    #         emitter.warning("\t[warning] variable " + var_name + " assigned random value")
    #         var_size = var_tuple['size']
    #         var_value = 0
    #         for i in range(1, var_size):
    #             var_value += ((2 << 7) << (int(i) - 1)) * random.randint(0, 255)
    #         input_var_list.append({"identifier": var_name, "value": var_value, "size": var_size})
    emitter.data("Generated Arg List", input_arg_list)
    emitter.data("Generated Var List", input_var_list)
    return input_arg_list, input_var_list


def generate_model_cli(formula):
    """
           This function will invoke the Z3 Cli interface to solve the provided formula and return the model byte list
           Arguments:
               formula: smtlib formatted formula
    """
    emitter.normal("\textracting z3 model")
    path_script = "/tmp/z3_script"
    path_result = "/tmp/z3_output"
    write_smtlib(formula, path_script)
    with open(path_script, "a") as script_file:
        script_file.writelines(["(get-model)\n", "(exit)\n"])
    z3_command = "z3 " + path_script + " > " + path_result
    execute_command(z3_command)
    with open(path_result, "r") as result_file:
        z3_output = result_file.readlines()

    model_byte_list = parser.parse_z3_output(z3_output)
    return model_byte_list


def generate_binary_file(byte_array):
    byte_list = []
    modified_index_list = []
    with open(values.CONF_PATH_POC, "rb") as poc_file:
        byte =poc_file.read(1)
        while byte:
            number = int(struct.unpack('>B', byte)[0])
            byte_list.append(number)
            byte = poc_file.read(1)
    emitter.data("Masked Byte List", values.MASK_BYTE_LIST)
    for index in byte_array:
        if index not in values.MASK_BYTE_LIST:
            byte_list[index] = byte_array[index]
            modified_index_list.append(index)
    emitter.data("Modified Byte List", modified_index_list)
    file_extension = str(values.CONF_PATH_POC).split(".")[-1]
    values.FILE_POC_GEN = definitions.DIRECTORY_OUTPUT + "/input-" + str(values.ITERATION_NO) + "." + file_extension

    with open(values.FILE_POC_GEN, "wb") as new_input_file:
        new_input_file.write(bytearray(byte_list))


def generate_formula(formula_str):
    parser = SmtLibParser()
    script = parser.get_script(cStringIO(formula_str))
    formula = script.get_last_formula()
    return formula


def generate_symbolic_paths(ppc_list):
    """
       This function will analyse the partial path conditions collected at each branch location and isolate
       the branch conditions added at each location, negate the constraint to create a new path
              ppc_list : a dictionary containing the partial path condition at each branch location
              returns a list of new partial path conditions
    """
    emitter.normal("\tgenerating new paths")
    path_list = list()
    path_count = 0
    result_list = parallel.generate_symbolic_paths_parallel(ppc_list)
    for result in result_list:
        path_count = path_count + 1
        path_list.append(result)

    emitter.highlight("\t\tgenerated " + str(path_count) + " flipped path(s)")
    return path_list


def generate_ktest(argument_list, second_var_list, print_output=False):
    """
    This function will generate the ktest file provided the argument list and second order variable list
        argument_list : a list containing each argument in the order that should be fed to the program
        second_var_list: a list of tuples where a tuple is (var identifier, var size, var value)
    """
    global File_Ktest_Path
    emitter.normal("\tgenerating ktest file")
    ktest_path = File_Ktest_Path
    ktest_command = "gen-bout --out-file {0}".format(ktest_path)

    for argument in argument_list:
        index = list(argument_list).index(argument)
        if "$POC" in argument:
            binary_file_path = values.CONF_PATH_POC
            if values.FILE_POC_GEN:
                binary_file_path = values.FILE_POC_GEN
            ktest_command += " --sym-file " + binary_file_path
        elif str(index) in values.CONF_MASK_ARG:
            continue
        else:
            ktest_command += " --sym-arg \"" + str(argument) + "\""

    for var in second_var_list:
        ktest_command += " --second-var \'{0}\' {1} {2}".format(var['identifier'], var['size'], var['value'])
    return_code = execute_command(ktest_command)
    return ktest_path, return_code


def generate_path_for_negation():
    constraint_list = []
    parser = SmtLibParser()
    emitter.normal("\tgenerating path for negation of patch constraint")
    for control_loc, sym_path in values.LIST_PPC:
        if control_loc == values.CONF_LOC_PATCH:
            script = parser.get_script(cStringIO(sym_path))
            formula = script.get_last_formula()
            patch_constraint = formula.arg(1)
            constraint_list.append(patch_constraint.serialize())

    last_sym_path = values.LAST_PPC_FORMULA
    # script = parser.get_script(cStringIO(last_sym_path))
    # formula = script.get_last_formula()
    negated_path = None
    while constraint_list:
        constraint = last_sym_path.arg(1)
        constraint_str = constraint.serialize()
        if constraint_str in constraint_list:
            constraint_list.remove(constraint_str)
            constraint = Not(constraint)
        if negated_path is None:
            negated_path = constraint
        else:
            negated_path = And(negated_path, constraint)
            last_sym_path = last_sym_path.arg(0)
    negated_path = And(negated_path, last_sym_path)
    return negated_path


def generate_patch_space(patch):
    partition_list = []
    partition = dict()
    patch_formula = extractor.extract_formula_from_patch(patch)
    var_list = list(patch_formula.get_free_variables())
    for var in var_list:
        if "const_" in str(var):
            constraint_info = dict()
            constraint_info['lower-bound'] = values.DEFAULT_PATCH_LOWER_BOUND
            constraint_info['upper-bound'] = values.DEFAULT_PATCH_UPPER_BOUND
            partition[str(var)] = constraint_info
    partition_list.append(partition)
    return partition_list


def generate_input_space(path_condition):
    partition = dict()
    var_list = generate_model(path_condition)
    for var in var_list:
        if "rvalue!" in str(var):
            constraint_info = dict()
            constraint_info['lower-bound'] = values.DEFAULT_INPUT_LOWER_BOUND
            constraint_info['upper-bound'] = values.DEFAULT_INPUT_UPPER_BOUND
            partition[str(var)] = constraint_info
    return partition


def generate_partition_for_patch_space(partition_model, patch_space, is_multi_dimension):
    partition_list = list()
    parameter_name = list(sorted(partition_model.keys()))[0]
    partition_value = partition_model[parameter_name]
    constraint_info = patch_space[parameter_name]
    constraint_info['name'] = parameter_name
    constraint_info['partition-value'] = partition_value
    param_partition_list = generate_partition_for_parameter(constraint_info, partition_value,
                                                            is_multi_dimension, parameter_name)
    del partition_model[parameter_name]
    if partition_model:
        partition_list_tmp = generate_partition_for_patch_space(partition_model, patch_space, is_multi_dimension)
        for partition_a in partition_list_tmp:
            for partition_b in param_partition_list:
                partition_b.update(partition_a)
                partition_list.append(copy.deepcopy(partition_b))
    else:
        if param_partition_list:
            partition_list = param_partition_list

    return partition_list


def generate_partition_for_input_space(partition_model, input_space, is_multi_dimension):
    partition_list = list()
    var_name = list(sorted(partition_model.keys()))[0]
    partition_value = partition_model[var_name]
    constraint_info = input_space[var_name]
    constraint_info['name'] = var_name
    constraint_info['partition-value'] = partition_value
    var_partition_list = generate_partition_for_input(constraint_info, partition_value,
                                                      is_multi_dimension, var_name)
    del partition_model[var_name]
    if partition_model:
        partition_list_tmp = generate_partition_for_input_space(partition_model, input_space, is_multi_dimension)
        for partition_a in partition_list_tmp:
            for partition_b in var_partition_list:
                partition_b.update(partition_a)
                partition_list.append(copy.deepcopy(partition_b))
    else:
        if var_partition_list:
            partition_list = var_partition_list

    return partition_list


def generate_partition_for_parameter(constraint_info, partition_value, is_multi_dimension, parameter_name):
    partition_list = list()
    partition_info = dict()
    range_info = dict()
    if is_multi_dimension:
        range_equal = (partition_value, partition_value)
        range_info['lower-bound'] = range_equal[0]
        range_info['upper-bound'] = range_equal[1]
        partition_info[parameter_name] = range_info
        partition_list.append(copy.deepcopy(partition_info))

    if constraint_info['lower-bound'] == constraint_info['upper-bound']:
        return partition_list
    range_lower = (constraint_info['lower-bound'], partition_value - 1)
    range_upper = (partition_value + 1, constraint_info['upper-bound'])

    if oracle.is_valid_range(range_lower):
        range_info['lower-bound'] = range_lower[0]
        range_info['upper-bound'] = range_lower[1]
        partition_info[parameter_name] = range_info
        partition_list.append(copy.deepcopy(partition_info))
    if oracle.is_valid_range(range_upper):
        range_info['lower-bound'] = range_upper[0]
        range_info['upper-bound'] = range_upper[1]
        partition_info[parameter_name] = range_info
        partition_list.append(copy.deepcopy(partition_info))

    return partition_list


def generate_partition_for_input(constraint_info, partition_value, is_multi_dimension, var_name):
    partition_list = list()
    partition_info = dict()
    range_info = dict()
    if is_multi_dimension:
        range_equal = (partition_value, partition_value)
        range_info['lower-bound'] = range_equal[0]
        range_info['upper-bound'] = range_equal[1]
        partition_info[var_name] = range_info
        partition_list.append(copy.deepcopy(partition_info))

    if constraint_info['lower-bound'] == constraint_info['upper-bound']:
        return partition_list
    range_lower = (constraint_info['lower-bound'], partition_value - 1)
    range_upper = (partition_value + 1, constraint_info['upper-bound'])

    if oracle.is_valid_range(range_lower):
        range_info['lower-bound'] = range_lower[0]
        range_info['upper-bound'] = range_lower[1]
        partition_info[var_name] = range_info
        partition_list.append(copy.deepcopy(partition_info))
    if oracle.is_valid_range(range_upper):
        range_info['lower-bound'] = range_upper[0]
        range_info['upper-bound'] = range_upper[1]
        partition_info[var_name] = range_info
        partition_list.append(copy.deepcopy(partition_info))

    return partition_list


def generate_constraint_for_patch_partition(patch_partition):
    formula = None
    for parameter_name in patch_partition:
        sym_var = Symbol(parameter_name, BV32)
        constraint_info = patch_partition[parameter_name]
        upper_bound = int(constraint_info['upper-bound'])
        lower_bound = int(constraint_info['lower-bound'])
        sub_formula = And(BVSGE(SBV(upper_bound, 32), sym_var), BVSLE(SBV(lower_bound, 32), sym_var))
        if formula is None:
            formula = sub_formula
        else:
            formula = And(formula, sub_formula)
    return formula


def generate_constraint_for_input_partition(input_partition):
    formula = None
    for var_name in input_partition:
        sym_array = Symbol(var_name, ArrayType(BV32, BV8))
        sym_var = BVConcat(Select(sym_array, BV(3, 32)),
                           BVConcat(Select(sym_array, BV(2, 32)),
                                    BVConcat(Select(sym_array, BV(1, 32)), Select(sym_array, BV(0, 32)))))
        constant_info = input_partition[var_name]
        upper_bound = int(constant_info['upper-bound'])
        lower_bound = int(constant_info['lower-bound'])
        sub_formula = And(BVSGE(SBV(upper_bound, 32), sym_var), BVSLE(SBV(lower_bound, 32), sym_var))
        if formula is None:
            formula = sub_formula
        else:
            formula = And(formula, sub_formula)
    return formula


def generate_constraint_for_input_space(input_space):
    formula = None
    for input_partition in input_space:
        sub_formula = generate_constraint_for_input_partition(input_partition)
        if formula is None:
            formula = sub_formula
        else:
            formula = Or(formula, sub_formula)
    return formula


def generate_constraint_for_patch_space(patch_space):
    formula = None
    for patch_partition in patch_space:
        sub_formula = generate_constraint_for_patch_partition(patch_partition)
        if formula is None:
            formula = sub_formula
        else:
            formula = Or(formula, sub_formula)
    return formula


# def generate_constraint_for_fixed_point(fixed_point_list):
#     formula = None
#     for var_name in fixed_point_list:
#         fixed_point = fixed_point_list[var_name]
#         sym_array = Symbol(var_name, ArrayType(BV32, BV8))
#         sym_var = BVConcat(Select(sym_array, BV(3, 32)),
#                  BVConcat(Select(sym_array, BV(2, 32)),
#                  BVConcat(Select(sym_array, BV(1, 32)), Select(sym_array, BV(0, 32)))))
#         sub_formula = Equals(sym_var, SBV(int(fixed_point), 32))
#         if formula is None:
#             formula = sub_formula
#         else:
#             formula = And(formula, sub_formula)
#     return formula
#
# def generate_new_range(constant_space, partition_list):
#     new_range_list = list()
#     constant_count = len(constant_space)
#     if constant_count == 1:
#         constant_name = list(constant_space.keys())[0]
#         constant_info = constant_space[constant_name]
#         is_continuous = constant_info['is_continuous']
#         partition_value = partition_list[constant_name]
#         if is_continuous:
#             range_lower = (constant_info['lower-bound'], partition_value - 1)
#             range_upper = (partition_value + 1, constant_info['upper-bound'])
#             if is_valid_range(range_lower):
#                 new_range_list.append((range_lower,))
#             if is_valid_range(range_upper):
#                 new_range_list.append((range_upper,))
#         else:
#             invalid_list = constant_info['invalid-list']
#             valid_list = constant_info['valid-list']
#             valid_list.remove(partition_value)
#             invalid_list.append(partition_value)
#             if valid_list:
#                 new_range_list.append((invalid_list,))
#
#     elif constant_count == 2:
#         constant_name_a = list(constant_space.keys())[0]
#         constant_name_b = list(constant_space.keys())[1]
#         constant_info_a = constant_space[constant_name_a]
#         is_continuous_a = constant_info_a['is_continuous']
#         partition_value_a = partition_list[constant_name_a]
#         constant_info_b = constant_space[constant_name_b]
#         partition_value_b = partition_list[constant_name_b]
#         is_continuous_b = constant_info_b['is_continuous']
#         if is_continuous_a:
#             range_lower_a = (constant_info_a['lower-bound'], partition_value_a - 1)
#             range_upper_a = (partition_value_a + 1, constant_info_a['upper-bound'])
#             if is_continuous_b:
#                 range_lower_b = (constant_info_b['lower-bound'], partition_value_b - 1)
#                 range_upper_b = (partition_value_b + 1, constant_info_b['upper-bound'])
#                 if is_valid_range(range_lower_a):
#                     if is_valid_range(range_lower_b):
#                         new_range_list.append((range_lower_a, range_lower_b))
#                     if is_valid_range(range_upper_b):
#                         new_range_list.append((range_lower_a, range_upper_b))
#
#                 if is_valid_range(range_upper_a):
#                     if is_valid_range(range_lower_b):
#                         new_range_list.append((range_upper_a, range_lower_b))
#                     if is_valid_range(range_upper_b):
#                         new_range_list.append((range_upper_a, range_upper_b))
#             else:
#                 invalid_list_b = constant_info_b['invalid-list']
#                 valid_list_b = constant_info_b['valid-list']
#                 valid_list_b.remove(partition_value_b)
#                 invalid_list_b.append(partition_value_b)
#                 if valid_list_b:
#                     if is_valid_range(range_lower_a):
#                         new_range_list.append((range_lower_a, invalid_list_b))
#                     if is_valid_range(range_upper_a):
#                         new_range_list.append((range_upper_a, invalid_list_b))
#
#         else:
#             if is_continuous_b:
#                 invalid_list_a = constant_info_a['invalid-list']
#                 valid_list_a = constant_info_a['valid-list']
#                 valid_list_a.remove(partition_value_a)
#                 invalid_list_a.append(partition_value_a)
#                 range_lower_b = (constant_info_b['lower-bound'], partition_value_b - 1)
#                 range_upper_b = (partition_value_b + 1, constant_info_b['upper-bound'])
#                 if valid_list_a:
#                     if is_valid_range(range_lower_b):
#                         new_range_list.append((invalid_list_a, range_lower_b))
#                     if is_valid_range(range_upper_b):
#                         new_range_list.append((invalid_list_a, range_upper_b))
#
#
#
#
#     elif constant_count == 3:
#         for constant_name_a in constant_space:
#             constant_info_a = constant_space[constant_name_a]
#             partition_value_a = partition_list[constant_name_a]
#             for constant_name_b in constant_space:
#                 constant_info_b = constant_space[constant_name_b]
#                 partition_value_b = partition_list[constant_name_b]
#                 for constant_name_c in constant_space:
#                     constant_info_c = constant_space[constant_name_c]
#                     partition_value_c = partition_list[constant_name_c]
#                     range_lower_a = (constant_info_a['lower-bound'], partition_value_a - 1)
#                     range_upper_a = (partition_value_a + 1, constant_info_a['upper-bound'])
#                     range_lower_b = (constant_info_b['lower-bound'], partition_value_b - 1)
#                     range_upper_b = (partition_value_b + 1, constant_info_b['upper-bound'])
#                     range_lower_c = (constant_info_c['lower-bound'], partition_value_c - 1)
#                     range_upper_c = (partition_value_c + 1, constant_info_c['upper-bound'])
#
#                     new_range_list.append((range_lower_a, range_lower_b, range_lower_c))
#                     new_range_list.append((range_lower_a, range_lower_b, range_upper_c))
#                     new_range_list.append((range_lower_a, range_upper_b, range_lower_c))
#                     new_range_list.append((range_lower_a, range_upper_b, range_upper_c))
#                     new_range_list.append((range_upper_a, range_lower_b, range_lower_c))
#                     new_range_list.append((range_upper_a, range_lower_b, range_upper_c))
#                     new_range_list.append((range_upper_a, range_upper_b, range_lower_c))
#                     new_range_list.append((range_upper_a, range_upper_b, range_upper_c))
#     else:
#         utilities.error_exit("unhandled constant count in generate new range")
#
#     return new_range_list


# def generate_formula_for_range(patch, constant_space, path_condition, assertion):
#     patch_constraint = extractor.extract_constraints_from_patch(patch)
#     constant_constraint = generator.generate_constant_constraint_formula(constant_space)
#     patch_constraint = And(patch_constraint, constant_constraint)
#     path_feasibility = And(path_condition, patch_constraint)
#     formula = And(path_feasibility, assertion)
#     return formula

def generate_assertion(assertion_temp, klee_dir):
    largest_path_condition = None
    max_obs = 0
    file_list = [f for f in os.listdir(klee_dir) if os.path.isfile(os.path.join(klee_dir, f))]
    for file_name in file_list:
        if ".smt2" in file_name:
            file_path = os.path.join(klee_dir, file_name)
            path_condition = extractor.extract_formula_from_file(file_path)
            model = generate_model(path_condition)
            var_list = list(model.keys())
            count_obs = 0
            declaration_line = assertion_temp[0]
            specification_line = assertion_temp[1]
            for var in var_list:
                if "obs!" in var:
                    count_obs = count_obs + 1
            if max_obs < count_obs:
                max_obs = count_obs
                largest_path_condition = path_condition
    declaration_line = assertion_temp[0]
    specification_line = assertion_temp[1]
    assertion_text = ""
    for index in range(0, max_obs):
        assertion_text = assertion_text + declaration_line.replace("obs!0", "obs!" + str(index))
        assertion_text = assertion_text + specification_line.replace("obs!0", "obs!" + str(index))
    specification_formula = generate_formula(assertion_text)
    return specification_formula, max_obs


def generate_extended_patch_formula(patch_formula, path_condition):
    model_path = generate_model(path_condition)
    var_list = list(model_path.keys())
    count = 0
    for var in var_list:
        if "angelic!bool" in var:
            count = count + 1
    input_list = list()

    path_script = "/tmp/z3_script"
    write_smtlib(patch_formula, path_script)
    with open(path_script, "r") as script_file:
        script_lines = script_file.readlines()
    script = "".join(script_lines)
    var_list = set(re.findall("\(declare-fun (.+?) \(\)", script))
    for var in var_list:
        if "constant" not in var:
            input_list.append(var)

    formula_txt = script
    formula_list = []
    for index in range(1, count):
        postfix = "_" + str(index)
        substituted_formula_txt = formula_txt
        for input_var in input_list:
            if "|" in input_var:
                input_var_postfix = input_var[:-1] + postfix + "|"
            else:
                input_var_postfix = input_var + postfix
            substituted_formula_txt = substituted_formula_txt.replace(input_var, input_var_postfix)
        formula = generate_formula(substituted_formula_txt)
        formula_list.append(formula)

    constraint_formula = patch_formula
    for formula in formula_list:
        constraint_formula = And(constraint_formula, formula)
    return constraint_formula


def generate_program_specification(binary_path):
    dir_list = [f for f in os.listdir(binary_path) if not os.path.isfile(os.path.join(binary_path, f))]
    expected_output_list = values.CONF_TEST_OUTPUT
    test_count = len(expected_output_list)
    max_skip_index = (test_count * 2) - 1
    program_specification = None
    for dir_name in dir_list:
        if "klee-out-" not in dir_name:
            continue
        dir_path = os.path.join(binary_path, dir_name)
        klee_index = int(dir_name.split("-")[-1])
        if klee_index <= max_skip_index:
            continue
        file_list = [f for f in os.listdir(dir_path) if os.path.isfile(os.path.join(dir_path, f))]
        for file_name in file_list:
            if ".smt2" in file_name:
                file_path = os.path.join(dir_path, file_name)
                path_condition = extractor.extract_formula_from_file(file_path)
                if program_specification is None:
                    program_specification = path_condition
                else:
                    program_specification = Or(program_specification, path_condition)

    return program_specification
