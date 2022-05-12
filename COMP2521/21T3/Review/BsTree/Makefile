
BsTree : testBsTree.o BsTree.o
	gcc -g -o BsTree testBsTree.o BsTree.o

testBsTree.o : testBsTree.c BsTree.h
	gcc -Wall -Werror -c testBsTree.c

BsTree.o : BsTree.c BsTree.h
	gcc -Wall -Werror -c BsTree.c
