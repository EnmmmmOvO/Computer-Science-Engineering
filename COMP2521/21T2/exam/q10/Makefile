# COMP2521 Final Exam
# equalBST

CC = gcc
CFLAGS = -Wall -Werror -g

all: testEqualBST

testEqualBST: testEqualBST.o equalBST.o BSTree.o
	$(CC) $(CFLAGS) -o testEqualBST testEqualBST.o equalBST.o BSTree.o

testEqualBST.o: testEqualBST.c BSTree.h
equalBST.o: equalBST.c BSTree.h
BSTree.o: BSTree.c BSTree.h

clean:
	rm -f testEqualBST *.o core

