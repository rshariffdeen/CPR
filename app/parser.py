from app import utilities, definitions, values, extractor
from pathlib import Path
import os
from app.synthesis import ComponentSymbol, collect_symbols, ComponentSemantics
from funcy import all_fn, any_fn, complement


def parse_z3_output(z3_output):
    """
           This function will read the output log of z3 cli interface and extract/parse the values of the model
           Arguments:
               z3_output: string output of the z3 cli invocation
    """
    model = dict()
    var_name = ""
    byte_list = dict()
    str_lambda = ""
    for line in z3_output:
        if "sat" in line or "model" in line:
            continue
        if "define-fun " in line or line == z3_output[-1]:
            if str_lambda:
                if "const" in str_lambda:
                    str_value = str_lambda.split("#x")[-1].split(")")[0]
                    byte_list = dict()
                    byte_list[0] = int("0x" + str_value, 16)
                elif "(lambda ((x!1 (_ BitVec 32))) #x" in str_lambda:
                    str_value = str_lambda.replace("(lambda ((x!1 (_ BitVec 32))) ", "").replace("))", "").replace("\n",
                                                                                                                   "")
                    byte_list[0] = int(str_value.replace("#", "0"), 16)
                elif "true)" in str_lambda:
                    byte_list[0] = int("0xff", 16)
                elif "false)" in str_lambda:
                    byte_list[0] = int("0x00", 16)
                elif "ite" in str_lambda:
                    max_index = 0
                    byte_list = dict()
                    token_list = str_lambda.split("(ite (= x!1 ")
                    for token in token_list[1:]:
                        if token.count("#x") == 2:
                            index, value = token.split(") ")
                        elif token.count("#x") == 3:
                            index, value, default = token.split(" ")
                            index = index.replace(")", "")
                            default = default.split(")")[0].replace("#", "0")
                        index = index.replace("#", "0")
                        value = value.replace("#", "0")
                        index = int(index, 16)
                        if index > max_index:
                            max_index = index
                        byte_list[index] = int(value, 16)

                    if max_index > 0:
                        byte_list.pop(max_index)
                        max_index = max_index - 1

                    for i in range(0, max_index):
                        if i not in byte_list:
                            byte_list[i] = int(default, 16)

                else:
                    print("Unhandled output")
                    print(str_lambda)
                    print(z3_output)
                    exit(1)

            if var_name and byte_list:
                model[var_name] = byte_list
                var_name = ""
                byte_list = dict()
            if line != z3_output[-1]:
                var_name = line.split("define-fun ")[1].split(" ()")[0]
                str_lambda = ""

        else:
            str_lambda += line

    return model


def parse_component_name(comp_str, count_constants):
    if comp_str in definitions.str_comp_map.keys():
        return definitions.str_comp_map[comp_str]
    elif comp_str in values.MAP_CUSTOM_COMPONENT_NAME.keys():
        return values.MAP_CUSTOM_COMPONENT_NAME[comp_str]
    elif str(comp_str).isnumeric():
        return "const_" + definitions.cust_comp_name_list[count_constants-1], count_constants - 1
    return None


def parse_component(comp_str, count_constants):
    comp_name, count_constants = parse_component_name(comp_str)
    if comp_name:
        if comp_name in values.MAP_COMPONENTS:
            return values.MAP_COMPONENTS[comp_name], count_constants
        else:
            utilities.error_exit("invalid component name: {}".format(comp_name))
    else:
        utilities.error_exit("invalid component string: {}".format(comp_str))


def parse_patch(left_tree, root_str, right_tree, count_constants):
    root_comp, count_constants = parse_component(root_str, count_constants)
    if len(left_tree) == 1:
        left_comp_tree, count_constants = parse_component(left_tree[0], count_constants)
    else:
        root_index = extractor.extract_root_index(left_tree)
        left_comp_tree, count_constants = parse_patch(left_tree[:root_index], left_tree[root_index], left_tree[root_index+1:], count_constants)

    if len(right_tree) == 1:
        right_comp_tree, count_constants = parse_component(right_tree[0], count_constants)
    else:
        root_index = extractor.extract_root_index(right_tree)
        right_comp_tree, count_constants = parse_patch(right_tree[:root_index], right_tree[root_index], right_tree[root_index + 1:], count_constants)

    # construct full patch
    holes = collect_symbols(root_comp[1], any_fn(ComponentSymbol.is_lhole, ComponentSymbol.is_rhole))
    if not holes:
        mappings = {}
    else:
        mappings = dict()
        mappings["right"] = right_comp_tree
        mappings["left"] = left_comp_tree
    patch_tree = (root_comp, mappings)
    return patch_tree, count_constants
