# COMP2521 ... Lab 03 Makefile

CC = gcc
CFLAGS = -Wall -Werror -g

.PHONY: all
all: sortIntList benchmarkArrayQueue benchmarkCircularArrayQueue

sortIntList:
	$(CC) $(CFLAGS) -o sortIntList sortIntList.c IntList.c

benchmarkArrayQueue:
	$(CC) $(CFLAGS) -o benchmarkArrayQueue benchmarkQueue.c ArrayQueue.c

benchmarkCircularArrayQueue:
	$(CC) $(CFLAGS) -o benchmarkCircularArrayQueue benchmarkQueue.c CircularArrayQueue.c

.PHONY: clean
clean:
	rm -rf sortIntList benchmarkArrayQueue benchmarkCircularArrayQueue

