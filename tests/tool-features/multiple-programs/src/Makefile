CC=$(TRIDENT_CC)
CFLAGS=-g -O0 -ftrapv

app_1: app_1.o util.o
	$(CC) -o app_1 app_1.o util.o
app_1.o: app_1.c util.h
	$(CC) -c -g app_1.c
app_2: app_2.o util.o
	$(CC) -o app_2 app_2.o util.o
app_2.o: app_2.c util.h
	$(CC) -c -g app_2.c
util.o: util.c util.h
	$(CC) -c -g util.c

all: app_2 app_1

clean:
	rm -f app_1 app_2
	rm -f *.bc
	rm -f .*.o
	rm -f .*.o.bc


