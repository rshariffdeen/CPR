# Manual #
CPR is a program repair tool for C/C++ programs. It generates a list of patches
that adhere to a provided user-specification and set initial test-cases, to fix any failing
test-case. It requires as input; patch-location, bug-location and list of variables/components 
to construct the patch. 

 ## Usage ##
CPR requires a configuration file as input which provides values as following:

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



One a configuration file is specified the tool can be invoked using the following command from the directory of the tool:
```
python3.7 CPR.py --conf=/path/to/conf/file
```

# Runtime Configuration Options
The tool supports the following runtime configurations:

    Usage: python3.7 CPR.py [OPTIONS] --conf=$FILE_PATH
	Options are:
		--debug	            | enable debugging information
		--mode=             | execution mode [0: sequential, 1: semi-paralle, 2: parallel] (default = 0)
		--dist-cal=	    | disable distance calculation (default=enabled)
		--selection=	    | selection strategy [0: deterministic, 1: random] (default=0)
		--dist-metric=	    | distance metric [0: control-loc, 1: statement] (default=0)
		--patch-type=	    | patch type [0: concrete, 1: abstract] (default=0)
		--refine-method=    | refine strategy [0: under-approx, 1: over-approx, 2: under-approx and over-approx, 3: none] (default=0)


### Side effects ###

**Warning!** CPR executes arbitrary modifications of your source code which may lead to undesirable side effects. Therefore, it is recommended to run CPR in an isolated environment.
Apart from that, CPR produces the following side effects:

- prints log messages on the standard error output
- saves generated patch(es) in the current directory (i.e. output)
- saves intermediate data in the current directory (i.e. tmp)
- saves various log information in the current directory (i.e. logs)
- transforms/builds/tests the provided project

Typically, it is safe to execute CPR consequently on the same copy of the project (without `make clean`), however idempotence cannot be guaranteed.
After CPR terminates successfully, it restores the original source files, but does not restore files generated/modified by the tests and the build system.
If CPR does not terminate successfully (e.g. by receiving `SIGKILL`), the source tree is likely to be corrupted.