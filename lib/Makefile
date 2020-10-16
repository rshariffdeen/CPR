CC=gcc
CFLAGS=-I $(KLEE_INCLUDE_PATH)

DEP = trident_runtime.h
SRC = trident_runtime.c
PROXY_C = trident_proxy.c
PROXY_OBJ = trident_proxy.o
OBJ_KLEE = $(SRC:%.c=%.o)

all: trident_runtime.o libtrident_runtime.a libtrident_runtime.so libtrident_runtime.bca libtrident_proxy.so libtrident_proxy.a libtrident_proxy.bca

%.o: %.c $(DEP)
	wllvm -g -fPIC -O0 -c -o $@ $< $(CFLAGS)

libtrident_proxy.so: $(PROXY_OBJ)
	wllvm -fPIC -shared -o $@ $(PROXY_OBJ)

libtrident_proxy.a: $(PROXY_OBJ)
	llvm-ar rcs $@ $(PROXY_OBJ)

libtrident_runtime.so: $(OBJ_KLEE)
	wllvm -fPIC -shared -o $@ $(OBJ_KLEE)

libtrident_runtime.a: $(OBJ_KLEE)
	llvm-ar rcs $@ $(OBJ_KLEE)

libtrident_runtime.bca: libtrident_runtime.a
	extract-bc libtrident_runtime.a

libtrident_proxy.bca: libtrident_proxy.a
	extract-bc libtrident_proxy.a

clean:
	rm -f *.o
	rm -f *.a
	rm -f *.bca
	rm -f *.so
