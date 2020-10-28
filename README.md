# FitReduce
Concolic Program Repair: A new automated program repair technique based on concolic execution
which works on patch abstraction with the sub-optimal goal of refinning the patch to less over-fit 
the initial test cases. 


## Build and Dependencies
We provide a ready-made container which includes all necessary envrionment set-up
to deploy and run our tool. Dependencies include:

* LLVM 3.4
* KLEE 1.4
* Python 3.6
* Z3Solver
* MathSAT Solver

Build and run a container:

    docker build -t fitreduce .
    docker run --rm -ti fitreduce /bin/bash


# Example
We provide several examples you can run to test our tool, all test cases are included
in the 'tests' directory. TODO: restructure test cases to a meaningful order

Run examples:

    python3.6 ConRepair.py --conf=tests/div-zero-1/repair.conf
    python3.6 ConRepair.py --conf=tests/div-zero-2/repair.conf

# Runtime Configuration Options
The tool supports the following functionality:

    Usage: python3.6 ConRepair.py [OPTIONS] --conf=$FILE_PATH
	Options are:
		--debug	            | enable debugging information
		--mode=             | execution mode [0: sequential, 1: semi-paralle, 2: parallel] (default = 0)
		--dist-cal=	    | disable distance calculation (default=enabled)
		--selection=	    | selection strategy [0: deterministic, 1: random] (default=0)
		--dist-metric=	    | distance metric [0: control-loc, 1: statement] (default=0)
		--patch-type=	    | patch type [0: concrete, 1: abstract] (default=0)
		--refine-method=    | refine strategy [0: under-approx, 1: over-approx, 2: under-approx and over-approx, 3: none] (default=0)

# Configuration Settings
The tool supports the following configuration:

    project_path:    absolute path to the project directory
    tag_id:     a tag to be used for the output files
    src_directory:  relative path to the source directory from the project directory
    binary_path:    relative path to the testing binary file from the project directory
    config_command:     custom config command (can opt out for the tool to automatically configure the project)
    build_command:      custom build command (can opt out for the tool to automatically build)
    test_input:     list of inputs for initial testing
    test_output:    expected output file for each test case
    custom_comp_list:   use of custom components to be added to the language
    spec_path:  relative path to the specification file
    loc_patch:  source code location of the patch
    loc_bug:    source code location of the bug
    general_comp_list:  list of components to be used for the patch from the language we support