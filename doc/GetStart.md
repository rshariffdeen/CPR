# Getting Started
Lets walk through a simple example ( a Hello World!) to understand how to use CPR.
Following is an example buggy code that could trigger a divide-by-zero error. 
The user input 'x' is not sanitized to check if it can trigger unwanted behavior.


## Sample Code
```c
#include <stdio.h>

int main(int argc, char *argv[]) {
  int x = atoi(argv[1]);
  int res, y;
  y = x - 1;
  res = 1000 / y;
  return 0;
}

```

Let's instrument this code for CPR to synthesise a patch and also to observe
a user-provided specification for correctness of the patch. 

### Instrumented Code
```c
#include <stdio.h>

#ifndef CPR_OUTPUT
#define CPR_OUTPUT(id, typestr, value) value
#endif

int main(int argc, char *argv[]) {
  int x = atoi(argv[1]);
  int res, y;
  if (__cpr_choice("L9", "bool", (int[]){x}, (char*[]){"x"}, 1, (int*[]){}, (char*[]){}, 0))  {
      return -1;
  }

  y = x - 1;

  CPR_OUTPUT("obs", "i32", y);
  res = 1000 / y;
  return 0;
}
```

There are two important instrumentation required by CPR in order to generate
a repair. First, CPR will synthesise an expression (in this case a boolean expression)
to repair the program, the placeholder template for the expression needs to be 
instrumented with the API call '__cpr_choice'. It takes 3 arguments; a location identifier,
type of expression and program variables for the expression. The location identifier is 
to distinguish the expression for multi-line fixes. The type of expression dictates the
components that can be used to synthesis the expression. For example; a boolean expression
can use comparison operators such as ">", "!=",  while integer expressions can use operators such
as "+", "/" etc. The last argument is a list of program variables to be used as
inputs for the repair expression. Second, CPR validates each synthesised repair expression based on a user-provided specification
which uses a program state/variable. "CPR_OUTPUT" function can be used to 
provide the necessary observation in the program. 

In our example, we need to validate the user provided input 'x', hence the patch
should be a validation check for 'x'. Our observation should be that 'y' should not
be '0', hence we instrument the code as shown above. 

We write the user-specification in SMT2 formula as shown below:
### User Specification
```
(declare-fun output!i32!obs!0 () (Array (_ BitVec 32) (_ BitVec 8) ) )
(assert (= false (= (concat  (select  output!i32!obs!0 (_ bv3 32) ) (concat  (select  output!i32!obs!0 (_ bv2 32) ) (concat  (select  output!i32!obs!0 (_ bv1 32) ) (select  output!i32!obs!0 (_ bv0 32) ) ) ) ) (_ bv0 32)) ))
```

We provide an initial test-case (a failing test-case) so CPR can fix the program
to pass the given test-case. 

### Expected Output
```
(declare-const obs!0 (_ BitVec 32))
(assert (= false (= obs!0 (_ bv0 32))))
```

We now write a configuration file using all this information:

### Configuration File
```
project_path:/concolic-repair/tests/synthesis/comparisons
tag_id:crash
src_directory:
binary_path:test
config_command:skip
build_command:make -e
test_input:1
test_output:t1.smt2
custom_comp_list:components/x.smt2,components/constant_a.smt2
general_comp_list:equal.smt2,not-equal.smt2,less-than.smt2,less-or-equal.smt2
spec_path:spec.smt2
depth:3
loc_patch:/concolic-repair/tests/synthesis/comparisons/test.c:10
loc_bug:/concolic-repair/tests/synthesis/comparisons/test.c:16
iterations:0
rank_limit:-1
```

### Running CPR
Now that we have setup everything, we run CPR to repair the sample program 

    pypy3 CPR.py --conf=path/to/conf/file


