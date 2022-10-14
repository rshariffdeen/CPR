PROGRAM=test
CC=$(CPR_CC)
CFLAGS=-g -O0 -ftrapv

%.o: %.c
	$(CC) -c -o $@ $< $(CFLAGS)

all: $(PROGRAM)

clean:
	rm -f $(PROGRAM)
	rm -f $(PROGRAM).bc
	rm -f .$(PROGRAM).o
	rm -f .$(PROGRAM).o.bc