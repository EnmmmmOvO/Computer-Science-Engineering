# COMP2521 Final Exam
# mergeOrdered

CC = gcc
CFLAGS = -Wall -Werror -g

all: testMergeOrdered

testMergeOrdered: testMergeOrdered.o mergeOrdered.o list.o
	$(CC) $(CFLAGS) -o testMergeOrdered testMergeOrdered.o mergeOrdered.o list.o

testMergeOrdered.o: testMergeOrdered.c list.h
mergeOrdered.o: mergeOrdered.c list.h
list.o: list.c list.h

clean:
	rm -f testMergeOrdered *.o core

