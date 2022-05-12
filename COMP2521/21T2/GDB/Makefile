
CC = gcc
CFLAGS = -Wall -Werror -g
LDFLAGS = -Wall -Werror -g

.PHONY: all
all: sorter testSet

sorter:	sorter.o
sorter.o: sorter.c

testSet: testSet.o Set.o
testSet.o: testSet.c Set.h
Set.o: Set.c Set.h

.PHONY: clean
clean:
	-rm -f sorter sorter.o
	-rm -f testSet testSet.o Set.o

