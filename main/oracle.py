import sys
from main import definitions, values


def did_program_crash(program_output):
    if any(crash_word in str(program_output).lower() for crash_word in definitions.crash_word_list):
        return True
    return False


def any_runtime_error(program_output):
    if any(error_word in str(program_output).lower() for error_word in definitions.error_word_list):
        return True
    return False


def is_loc_on_stack(source_path, function_name, line_number, stack_info):
    # print(source_path, function_name, line_number)
    if source_path in stack_info.keys():
        # print(source_path)
        source_info = stack_info[source_path]
        if function_name in source_info.keys():
            # print(function_name)
            line_list = source_info[function_name]
            # print(line_list)
            if str(line_number) in line_list:
                # print(line_number)
                return True
    return False


def is_loc_on_sanitizer(source_path, line_number, suspicious_lines):
    # print(source_path, line_number)
    # print(suspicious_lines)
    source_loc = source_path + ":" + str(line_number)
    if source_loc in suspicious_lines.keys():
        return True
    return False


def is_loc_in_trace(source_loc):
    return source_loc in values.LIST_TRACE

