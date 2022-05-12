# COMP2521 Final Exam
# nodesNotBalanced

CC = gcc
CFLAGS = -Wall -Werror -g

all: testNodesNotBalanced

testNodesNotBalanced: testNodesNotBalanced.o nodesNotBalanced.o BSTree.o
	$(CC) $(CFLAGS) -o testNodesNotBalanced testNodesNotBalanced.o nodesNotBalanced.o BSTree.o

testNodesNotBalanced.o: testNodesNotBalanced.c BSTree.h 
nodesNotBalanced.o: nodesNotBalanced.c BSTree.h 
BSTree.o: BSTree.c BSTree.h 

clean:
	rm -f testNodesNotBalanced *.o core

