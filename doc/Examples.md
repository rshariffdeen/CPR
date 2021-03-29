# Example Usage
In this document we provide examples of how to use CPR with prepared 
test cases to elaborate the capabilities of CPR. Following details explain
the test-cases we provide in our repository. Please take a look at the
page Getting Started to understand how to use CPR. 

## Synthesis
CPR can synthesise boolean and integer expressions using a set of components
that are easily extensible by anyone. We provide readily available
set of general component, on which other components can be extended upon.


### Examples of Boolean Expression
    pypy3 CPR.py --conf=tests/synthesis/comparisons/repair.conf
    pypy3 CPR.py --conf=tests/synthesis/logical-connectors/repair.conf


### Example of Integer Expression
    pypy3 CPR.py --conf=tests/synthesis/integer-expressions/repair.conf


## User Specification
CPR requires a user-specification to generate the initial set of patches and
optionally initial test-cases can be provided for more efficient search for
the correct repair. User can provide the initial test-cases in multiple forms.

### Exploit for Test Input
    pypy3 CPR.py --conf=tests/user-specification/exploit/repair.conf

### Set of Values for Test Inputs
    pypy3 CPR.py --conf=tests/user-specification/test-cases/repair.conf

### Strings in a File for Test Inputs
    pypy3 CPR.py --conf=tests/user-specification/test-suite-file/repair.conf

### Directory with Files for Test Inputs
    pypy3 CPR.py --conf=tests/user-specification/test-suite-dir/repair.conf
