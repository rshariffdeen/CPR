import os
import collections
from main import emitter

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


def collect_symbolic_path(log_path, project_path):
    """
       This function will read the output log of a klee concolic execution and extract the partial path conditions
    """
    emitter.normal("\textracting path conditions")
    ppc_list = collections.OrderedDict()
    last_sym_path = ""
    if os.path.exists(log_path):
        source_path = ""
        path_condition = ""
        with open(log_path, 'r') as trace_file:
            for line in trace_file:
                if '[path:ppc]' in line:
                    if project_path in line:
                        source_path = str(line.replace("[path:ppc]", '')).split(" : ")[0]
                        source_path = source_path.strip()
                        source_path = os.path.abspath(source_path)
                        path_condition = str(line.replace("[path:ppc]", '')).split(" : ")[1]
                        continue
                if source_path:
                    if "(exit)" not in line:
                        path_condition = path_condition + line
                    else:
                        if source_path not in ppc_list.keys():
                            ppc_list[source_path] = list()
                        ppc_list[source_path].append((path_condition))
                        last_sym_path = path_condition
                        source_path = ""
                        path_condition = ""
    # constraints['last-sym-path'] = last_sym_path
    # print(constraints.keys())
    return ppc_list, last_sym_path


def collect_trace(file_path, project_path):
    """
       This function will read the output log of a klee concolic execution and extract the instruction trace
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
    return list_trace
