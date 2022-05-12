# COMP2521 ... Lab 03 Makefile

# !!! DO NOT MODIFY THIS FILE !!!

CC = gcc
CFLAGS = -Wall -Werror -g

.PHONY: all
all: sortIntList benchmarkArrayQueue benchmarkCircularArrayQueue

sortIntList: sortIntList.c IntList.c IntList.h
	$(CC) $(CFLAGS) -o sortIntList sortIntList.c IntList.c

benchmarkArrayQueue: benchmarkQueue.c ArrayQueue.c Queue.h
	$(CC) $(CFLAGS) -o benchmarkArrayQueue benchmarkQueue.c ArrayQueue.c

benchmarkCircularArrayQueue: benchmarkQueue.c CircularArrayQueue.c Queue.h
	$(CC) $(CFLAGS) -o benchmarkCircularArrayQueue benchmarkQueue.c CircularArrayQueue.c

.PHONY: clean
clean:
	rm -rf sortIntList benchmarkArrayQueue benchmarkCircularArrayQueue

