import os
import time
from main import emitter, logger, definitions, values, builder, repair
from main.utilities import error_exit, extract_byte_code
from main.concolic import run_concrete_execution, run_concolic_execution


def create_directories():
    if not os.path.isdir(definitions.DIRECTORY_LOG):
        os.makedirs(definitions.DIRECTORY_LOG)

    if not os.path.isdir(definitions.DIRECTORY_OUTPUT_BASE):
        os.makedirs(definitions.DIRECTORY_OUTPUT_BASE)

    if not os.path.isdir(definitions.DIRECTORY_BACKUP):
        os.makedirs(definitions.DIRECTORY_BACKUP)

    if not os.path.isdir(definitions.DIRECTORY_TMP):
        os.makedirs(definitions.DIRECTORY_TMP)


def read_conf(arg_list):
    emitter.normal("reading configuration values from arguments")
    if len(arg_list) > 0:
        for arg in arg_list:
            if definitions.ARG_DEBUG in arg:
                values.DEBUG = True
            elif definitions.ARG_CONF_FILE in arg:
                values.FILE_CONFIGURATION = str(arg).replace(definitions.ARG_CONF_FILE, '')
            else:
                emitter.error("Invalid argument: " + arg)
                emitter.help()
                exit()
    else:
        emitter.help()
        exit()


def read_conf_file():
    emitter.normal("reading configuration values form configuration file")
    if not os.path.exists(values.FILE_CONFIGURATION):
        emitter.error("[NOT FOUND] Configuration file " + values.FILE_CONFIGURATION)
        exit()
    if os.path.getsize(values.FILE_CONFIGURATION) == 0:
        emitter.error("[EMPTY] Configuration file " + values.FILE_CONFIGURATION)
        exit()
    with open(values.FILE_CONFIGURATION, 'r') as conf_file:
        configuration_list = [i.strip() for i in conf_file.readlines()]

    for configuration in configuration_list:
        if definitions.CONF_PATH_PROGRAM in configuration:
            values.CONF_PATH_PROGRAM = configuration.replace(definitions.CONF_PATH_PROGRAM, '')
        elif definitions.CONF_NAME_PROGRAM in configuration:
            values.CONF_NAME_PROGRAM = configuration.replace(definitions.CONF_NAME_PROGRAM, '')
        elif definitions.CONF_COMMAND_BUILD in configuration:
            values.CONF_COMMAND_BUILD = configuration.replace(definitions.CONF_COMMAND_BUILD, '')
        elif definitions.CONF_COMMAND_CONFIG in configuration:
            values.CONF_COMMAND_CONFIG = configuration.replace(definitions.CONF_COMMAND_CONFIG, '')
        elif definitions.CONF_TEST_FILE in configuration:
            values.CONF_TEST_FILE = configuration.replace(definitions.CONF_TEST_FILE, '')
            if not os.path.isfile(values.CONF_TEST_FILE):
                error_exit("Test file " + values.CONF_TEST_FILE + " not found")
        elif definitions.CONF_TEST_INPUT in configuration:
            values.CONF_TEST_INPUT = configuration.replace(definitions.CONF_TEST_INPUT, '')
            values.ARGUMENT_LIST = values.CONF_TEST_INPUT


def bootstrap(arg_list):
    emitter.title("Starting " + values.TOOL_NAME)
    emitter.sub_title("Loading Configurations")
    read_conf(arg_list)
    read_conf_file()


def initialize():
    emitter.title("Initializing Program")
    program_path = values.CONF_PATH_PROGRAM + "/" + values.CONF_NAME_PROGRAM
    argument_list = values.CONF_TEST_INPUT.split(",")
    emitter.debug("input list in test case:", argument_list)

    # ktest_path, exit_code = generate_ktest(argument_list, {})
    # assert int(exit_code) == 0
    # assert os.path.isfile(ktest_path)
    # assert os.path.getsize(ktest_path) > 0
    emitter.sub_title("Running initial concrete execution")
    extract_byte_code(program_path)
    exit_code = run_concrete_execution(program_path + ".bc", argument_list, {}, True)
    assert exit_code == 0
    #
    # klee_file_1 = cwd + "/klee-out-0/test000001.smt2"
    # assert os.path.isfile(klee_file_1)
    # assert os.path.getsize(klee_file_1) > 0
    emitter.sub_title("Running initial concolic Execution")
    extract_byte_code(program_path)
    exit_code = run_concolic_execution(program_path + ".bc", argument_list, {}, True)

    assert exit_code == 0


def main(arg_list):
    create_directories()
    emitter.start()
    start_time = time.time()
    time_info = dict()
    time_check = time.time()
    bootstrap(arg_list)
    time_info[definitions.KEY_DURATION_BOOTSTRAP] = str(time.time() - time_check)

    time_check = time.time()
    builder.build_normal()
    assert os.path.isfile(values.CONF_PATH_PROGRAM + "/" + values.CONF_NAME_PROGRAM)
    assert os.path.getsize(values.CONF_PATH_PROGRAM + "/" + values.CONF_NAME_PROGRAM) > 0
    time_info[definitions.KEY_DURATION_BUILD] = str(time.time() - time_check)

    time_check = time.time()
    initialize()
    time_info[definitions.KEY_DURATION_INITIALIZATION] = str(time.time() - time_check)

    time_check = time.time()
    repair.run(values.CONF_PATH_PROGRAM, values.CONF_NAME_PROGRAM)
    time_info[definitions.KEY_DURATION_REPAIR] = str(time.time() - time_check)

    project_path = "/concolic-repair/tests/example"
    program = "test"

    assertion = "path_to_assertion_file"  # TODO

    ## Prepare the program under test.
    init(project_path, program)

    ## Generate all possible solutions by running the synthesizer.
    P = generate_patch_set(project_path)
    print("|P|=" + str(len(P)))

    ## This is a dummy call to produce the first results.
    global list_path_explored, list_path_detected
    second_var_list = [{"identifier": "x", "value": 1, "size": 4}]
    argument_list = [1]
    run_concolic_execution(program + ".bc", argument_list, second_var_list, True)
    ppc_log_path = project_path + "/klee-last/ppc.log"
    expr_log_path = project_path + "/klee-last/expr.log"

    print(">> start repair loop")

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

        gen_arg_list, gen_var_list = generate_new_input(ppc_log_path, expr_log_path, project_path, argument_list,
                                                        second_var_list,
                                                        substituted_patch)  # TODO (later) patch candidate missing
        assert gen_arg_list  # there should be a concrete input
        print(">> new input: " + str(gen_arg_list))

        ## Concolic execution of concrete input and patch candidate to retrieve path constraint.
        exit_code = run_concolic_execution(program + ".bc", gen_arg_list, gen_var_list)
        assert exit_code == 0

        ## Reduces the set of patch candidates based on the current path constraint
        P = reduce(P, project_path + "/klee-last/", gen_arg_list, assertion)
        print("|P|=" + str(len(P)))

        # Checks for the current coverage.
        satisfied = checkCoverage()

        # Final running time and exit message
        time_info[definitions.KEY_DURATION_TOTAL] = str(time.time() - start_time)
        emitter.end(time_info)
        logger.end(time_info)


if __name__ == "__main__":
    import sys
    main(sys.argv[1:])
