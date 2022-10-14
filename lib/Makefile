CC=gcc
CFLAGS=-I $(KLEE_INCLUDE_PATH)

DEP = cpr_runtime.h
SRC = cpr_runtime.c
PROXY_C = cpr_proxy.c
PROXY_OBJ = cpr_proxy.o
OBJ_KLEE = $(SRC:%.c=%.o)

all: cpr_runtime.o libcpr_runtime.a libcpr_runtime.so libcpr_runtime.bca libcpr_proxy.so libcpr_proxy.a libcpr_proxy.bca

%.o: %.c $(DEP)
	wllvm -g -fPIC -O0 -c -o $@ $< $(CFLAGS)

libcpr_proxy.so: $(PROXY_OBJ)
	wllvm -fPIC -shared -o $@ $(PROXY_OBJ)

libcpr_proxy.a: $(PROXY_OBJ)
	llvm-ar rcs $@ $(PROXY_OBJ)

libcpr_runtime.so: $(OBJ_KLEE)
	wllvm -fPIC -shared -o $@ $(OBJ_KLEE)

libcpr_runtime.a: $(OBJ_KLEE)
	llvm-ar rcs $@ $(OBJ_KLEE)

libcpr_runtime.bca: libcpr_runtime.a
	extract-bc libcpr_runtime.a

libcpr_proxy.bca: libcpr_proxy.a
	extract-bc libcpr_proxy.a

clean:
	rm -f *.o
	rm -f *.a
	rm -f *.bca
	rm -f *.so
