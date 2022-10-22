import json
import pickle
import re
from app import emitter, definitions, values
from six.moves import cStringIO
import os
from pysmt.smtlib.parser import SmtLibParser


def read_json(file_path):
    json_data = None
    if os.path.isfile(file_path):
        with open(file_path, 'r') as in_file:
            content = in_file.readline()
            json_data = json.loads(content)
    return json_data


def read_pickle(file_path):
    pickle_object = None
    if os.path.isfile(file_path):
        with open(file_path, 'rb') as pickle_file:
            pickle_object = pickle.load(pickle_file)
    return pickle_object


def collect_symbolic_expression(log_path):
    """
       This function will read the output log of a klee concolic execution and extract symbolic expressions
       of variables of interest
    """
    # emitter.normal("\textracting symbolic expressions")
    var_expr_map = list()
    if os.path.exists(log_path):
        with open(log_path, 'r') as trace_file:
            expr_pair = None
            for line in trace_file:
                if '[klee:expr]' in line:
                    line = line.split("[klee:expr] ")[-1]
                    if "[var-type]" in line:
                        continue
                    var_name, var_expr = line.split(" : ")
                    var_expr = var_expr.replace("\n", "")
                    if "[program-var]" in var_name:
                        var_name = var_name.replace("[program-var] ", "")
                        expr_pair = (var_name, var_expr)
                    elif "[angelic-var]" in var_name:
                        var_name = var_name.replace("[angelic-var] ", "")
                        expr_pair = (expr_pair, (var_name, var_expr))
                        if expr_pair not in var_expr_map:
                            var_expr_map.append(expr_pair)
    return var_expr_map


def collect_symbolic_path_prefix(log_path, project_path):
    """
       This function will read the output log of a klee concolic execution and
       extract the prefix of partial path condition that should be omitted in path generation
    """
    emitter.normal("\textracting prefix of path condition")
    prefix_ppc = ""
    if os.path.exists(log_path):
        source_path = ""
        path_condition = ""
        with open(log_path, 'r') as trace_file:
            for line in trace_file:
                if '[path:ppc]' in line:
                    if project_path in line:
                        break
                    else:
                        source_path = str(line.replace("[path:ppc]", '')).split(" : ")[0]
                        source_path = source_path.strip()
                        source_path = os.path.abspath(source_path)
                        path_condition = str(line.replace("[path:ppc]", '')).split(" : ")[1]
                        continue

                if source_path:
                    if "(exit)" not in line:
                        path_condition = path_condition + line
                    else:
                        prefix_ppc = path_condition
                        source_path = ""
                        path_condition = ""
    return prefix_ppc


def collect_symbolic_path(log_path, project_path):
    """
       This function will read the output log of a klee concolic execution and
       extract the partial path conditions
    """
    emitter.normal("\textracting path conditions")
    ppc_list = list()
    last_sym_path = ""
    if os.path.exists(log_path):
        source_path = ""
        path_condition = ""
        with open(log_path, 'r') as trace_file:
            for line in trace_file:
                if '[path:ppc]' in line:
                    if project_path in line or definitions.DIRECTORY_LIB in line:
                        source_path = str(line.replace("[path:ppc]", '')).split(" : ")[0]
                        source_path = source_path.strip()
                        source_path = os.path.abspath(source_path)
                        path_condition = str(line.replace("[path:ppc]", '')).split(" : ")[1]
                        continue
                if source_path:
                    if "(exit)" not in line:
                        path_condition = path_condition + line
                    else:
                        ppc_list.append((source_path, path_condition))
                        last_sym_path = path_condition
                        source_path = ""
                        path_condition = ""
    # constraints['last-sym-path'] = last_sym_path
    # print(constraints.keys())
    parser = SmtLibParser()
    script = parser.get_script(cStringIO(last_sym_path))
    formula = script.get_last_formula()
    return ppc_list, formula


def collect_trace(file_path, project_path):
    """
       This function will read the output log of a klee concolic execution and
       extract the instruction trace
    """
    emitter.normal("\textracting instruction trace")
    list_trace = list()
    if os.path.exists(file_path):
        with open(file_path, 'r') as trace_file:
            for line in trace_file:
                if '[klee:trace]' in line:
                    if project_path in line:
                        trace_line = str(line.replace("[klee:trace] ", ''))
                        trace_line = trace_line.strip()
                        source_path, line_number = trace_line.split(":")
                        source_path = os.path.abspath(source_path)
                        trace_line = source_path + ":" + str(line_number)
                        if (not list_trace) or (list_trace[-1] != trace_line):
                            list_trace.append(trace_line)
    if values.CONF_LOC_PATCH:
        if os.path.abspath(values.CONF_LOC_PATCH) in list_trace:
            emitter.note("\t\t[note] patch location detected in trace")
            values.COUNT_HIT_PATCH_LOC = values.COUNT_HIT_PATCH_LOC + 1
    if values.CONF_LOC_BUG:
        if os.path.abspath(values.CONF_LOC_BUG) in list_trace:
            emitter.note("\t\t[note] fault location detected in trace")
            values.COUNT_HIT_BUG_LOG = values.COUNT_HIT_BUG_LOG + 1
    if values.CONF_LOC_LIST_CRASH:
        if not set(values.CONF_LOC_LIST_CRASH).isdisjoint(list_trace):
            emitter.note("\t\t[note] a crash location detected in trace")
            values.COUNT_HIT_CRASH_LOC = values.COUNT_HIT_CRASH_LOC + 1
    is_crash = collect_crash_point(values.FILE_MESSAGE_LOG)
    if is_crash:
        values.IS_CRASH = True
        values.COUNT_HIT_CRASH = values.COUNT_HIT_CRASH + 1
        emitter.note("\t\t[note] program crashed")
    else:
        values.IS_CRASH = False
        emitter.note("\t\t[note] program did not crash")
    return list_trace


def collect_symbolic_path_loc(log_path, project_path):
    """
       This function will read the output log of a klee concolic execution and
       extract the partial path condition insert locations (i.e. control location)
    """
    emitter.normal("\textracting path conditions")
    ppc_loc_list = list()
    if os.path.exists(log_path):
        with open(log_path, 'r') as trace_file:
            for line in trace_file:
                if '[path:ppc]' in line:
                    if project_path in line or definitions.DIRECTORY_LIB in line:
                        source_path = str(line.replace("[path:ppc]", '')).split(" : ")[0]
                        source_path = source_path.strip()
                        source_path = os.path.abspath(source_path)
                        ppc_loc_list.append(source_path)
    return ppc_loc_list


def collect_concretized_bytes(log_path):
    concretized_info = dict()
    if os.path.exists(log_path):
        with open(log_path, 'r') as trace_file:
            for read_line in trace_file:
                if "[concretizing]" in read_line:
                    read_line = read_line.replace("[concretizing] ", "")
                    if "A-data" in read_line:
                        if "A-data" not in concretized_info:
                            concretized_info["A-data"] = set()
                        index = int(read_line.split("[")[1].replace("]",""))
                        concretized_info["A-data"].add(index)
    return concretized_info


def collect_bytes_from_smt2(file_path):
    index_list = list()
    if os.path.exists(file_path):
        with open(file_path, 'r') as smt2_file:
            str_txt = smt2_file.readlines()
        str_txt = "".join(str_txt)
        index_list = list(set(re.findall("\(select  A-data \(\_ bv(.+?) 32\) ", str_txt)))
    return sorted(index_list)


def collect_crash_point(trace_file_path):
    """
        This function will read the output log of a klee concolic execution and
        extract the location of the crash instruction
     """
    crash_location = ""
    if os.path.exists(trace_file_path):
        with open(trace_file_path, 'r') as trace_file:
            for read_line in trace_file:
                if "KLEE: ERROR:" in read_line:
                    read_line = read_line.replace("KLEE: ERROR: ", "")
                    crash_location = read_line.split(": ")[0]
                    break
    return crash_location


def collect_exploit_return_code(output_file_path):
    """
        This function will read the output log of a program execution
        and extract the exit code of the program
    """
    return_code = ""
    if os.path.exists(output_file_path):
        with open(output_file_path, 'r') as output_file:
            for read_line in output_file.readlines():
                if "RETURN CODE:" in read_line:
                    read_line = read_line.replace("RETURN CODE: ", "")
                    return_code = int(read_line)
                    break
    return return_code


def collect_exploit_output(output_file_path):
    """
        This function will read the output log of a program execution
        and extract the output text
    """
    output = ""
    if os.path.exists(output_file_path):
        with open(output_file_path, 'r') as output_file:
            output = output_file.readlines()
    return output


def collect_stack_info(trace_file_path):
    """
        This function will read the output log of a klee concolic execution
        and extract any stack information avail for error exits
    """
    stack_map = dict()
    if os.path.exists(trace_file_path):
        with open(trace_file_path, 'r') as trace_file:
            is_stack = False
            for read_line in trace_file:
                if is_stack and '#' in read_line:
                    if " at " in read_line:
                        read_line, source_path = str(read_line).split(" at ")
                        source_path, line_number = source_path.split(":")
                        function_name = str(read_line.split(" in ")[1]).split(" (")[0]
                        if source_path not in stack_map.keys():
                            stack_map[source_path] = dict()
                        stack_map[source_path][function_name] = line_number.strip()
                if "Stack:" in read_line:
                    is_stack = True
                    continue
    return stack_map


def read_bit_length(log_file_path):
    bit_length_list = dict()
    if os.path.exists(log_file_path):
        with open(log_file_path, 'r') as log_file:
            line_list = log_file.readlines()
            var_name = ""
            var_length = 0
            for line in line_list:
                if "name:" in line:
                    var_name = line.split("name: ")[-1].strip().replace("'", "")
                elif "size:" in line:
                    var_length = int(line.split("size: ")[-1].strip().replace("'", ""))

                if var_name and var_length > 0:
                    bit_length_list[var_name] = var_length
                    var_name = ""
                    var_length = 0

    return bit_length_list


def collect_specification(spec_file_path):
    spec_lines = list()
    if os.path.exists(spec_file_path):
        with open(spec_file_path, 'r') as spec_file:
            spec_lines = spec_file.readlines()
    return spec_lines


def read_patch_list(dir_patch):
    patch_list = []
    if os.path.isdir(dir_patch):
        file_list = [f for f in os.listdir(dir_patch) if os.path.isfile(os.path.join(dir_patch, f))]
        for patch_path in file_list:
            if ".patch" in patch_path:
                with open(patch_path, "r") as p_file:
                    patch_line = p_file.readline().split("---> ")[-1].replace("\"", "")
                    patch_list.append(patch_line)
    return patch_list
