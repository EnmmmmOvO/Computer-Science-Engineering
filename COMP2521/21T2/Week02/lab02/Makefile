# COMP2521 ... Lab 02 Makefile

CC = gcc
CFLAGS = -Wall -Werror -g

all: testListQueue testArrayQueue testCircularArrayQueue

testListQueue: testQueue.o ListQueue.o
	$(CC) $(CFLAGS) -o testListQueue testQueue.o ListQueue.o

testArrayQueue: testQueue.o ArrayQueue.o
	$(CC) $(CFLAGS) -o testArrayQueue testQueue.o ArrayQueue.o

testCircularArrayQueue: testQueue.o CircularArrayQueue.o
	$(CC) $(CFLAGS) -o testCircularArrayQueue testQueue.o CircularArrayQueue.o

testQueue.o: testQueue.c Queue.h

ListQueue.o: ListQueue.c Queue.h
ArrayQueue.o: ArrayQueue.c Queue.h
CircularArrayQueue.o: CircularArrayQueue.c Queue.h

.PHONY: clean
clean:
	rm -f testListQueue testArrayQueue testCircularArrayQueue
	rm -f *.o

