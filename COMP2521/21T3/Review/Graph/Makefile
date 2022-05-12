test : test.o Stack.o
	gcc -g -o test test.o Stack.o

test.o : test.c Stack.h
	gcc -g -Wall -Werror -c test.c

Stack.o : Stack.c Stack.h
	gcc -g -Wall -Werror -c Stack.c

Queue.o : Queue.c Queue.h
	gcc -g -Wall -Werror -c Queue.c