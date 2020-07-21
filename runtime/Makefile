CC=gcc
CFLAGS=-I $(KLEE_INCLUDE_PATH)

DEP = trident_runtime.h
SRC = trident_runtime.c
OBJ_KLEE = $(SRC:%.c=%.o)

all: trident_runtime.o libtrident_runtime.a

%.o: %.c $(DEP)
	wllvm -g -O0 -c -o $@ $< $(CFLAGS)

libtrident_runtime.a: $(OBJ_KLEE)
	llvm-ar rcs $@ $(OBJ_KLEE)

clean:
	rm -f *.o
	rm -f *.a