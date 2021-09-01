from app import utilities, definitions, values
from pathlib import Path


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


def parse_component(comp_str):
    str_comp_map = {
        "==": "equal", "+": "addition", "=": "assignment", "&" : "bitwise-and",
        "|": "bitwise-or", "~": "bitwise-not", "/": "division", ">=": "greater-or-equal",
        ">": "greater-than", "<=": "less-or-equal", "&&": "logical-and", "||": "logical-or",
        "!": "logical-not", "-": "subtraction", "*": "multiplication", "!=": "not-equal",
        "<": "less-than"
                    }
    if comp_str in str_comp_map.keys():
        return str_comp_map[comp_str]
    return None


def parse_component_list(comp_str_list):
    custom_comp_str_list = []
    general_comp_str_list = []
    for comp_str in comp_str_list:
        if str(comp_str).isalnum():
            comp_name = values.MAP_CUSTOM_COMPONENT[comp_str]
            custom_comp_str_list.append(Path(definitions.DIRECTORY_COMPONENTS_CUSTOM + "/" + comp_name + ".smt2"))
        else:
            gen_comp_name = parse_component(comp_str)
            if gen_comp_name is None:
                utilities.error_exit("Incompatible General Component Detected: {}".format(comp_str))
            general_comp_str_list.append(gen_comp_name)
    return general_comp_str_list, custom_comp_str_list

