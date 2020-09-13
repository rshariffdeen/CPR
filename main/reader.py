import os
import collections
from main import emitter, definitions, values


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
                    if project_path in line or definitions.DIRECTORY_RUNTIME in line:
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
    return ppc_list.reverse(), last_sym_path


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
        if values.CONF_LOC_PATCH in list_trace:
            emitter.warning("\t\t[note] patch location detected in trace")
    if values.CONF_LOC_BUG:
        if values.CONF_LOC_BUG in list_trace:
            emitter.warning("\t\t[note] fault location detected in trace")
    return list_trace


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

