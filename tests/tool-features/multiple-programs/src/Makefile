CC=$(CPR_CC)

all:
	$(CC) -c -g util.c
	extract-bc util.o
	$(CC) -c -g app_1.c
	extract-bc app_1.o
	$(CC) -c -g app_2.c
	extract-bc app_2.o
	$(CC) -c -g app_3.c
	extract-bc app_3.o
	$(CC) -o app_1 app_1.o util.o
	$(CC) -o app_2 app_2.o util.o
	$(CC) -o app_3 app_3.o util.o
	extract-bc app_1
	extract-bc app_2
	extract-bc app_3

clean:
	rm -f app_1 app_2 app_3
	rm -f *.bc
	rm -f *.o
	rm -f *.o.bc
