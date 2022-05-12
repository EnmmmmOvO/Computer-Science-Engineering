BTree : testBTree.o BTree.o
	gcc -g -o BTree testBTree.o BTree.o

testBTree.o : testBTree.c BTree.h
	gcc -g -Wall -Werror -c testBTree.c

BTree.o : BTree.c BTree.h
	gcc -g -Wall -Werror -c BTree.c

