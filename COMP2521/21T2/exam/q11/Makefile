# COMP2521 Final Exam
# printWords

CC = gcc
CFLAGS = -Wall -Werror -g

all: testTriePrintWords

testTriePrintWords: testTriePrintWords.o printWords.o Trie.o
	$(CC) $(CFLAGS) -o testTriePrintWords testTriePrintWords.o printWords.o Trie.o

testTriePrintWords.o: testTriePrintWords.c Trie.h
printWords.o: printWords.c Trie.h
Trie.o: Trie.c Trie.h

clean:
	rm -f testTriePrintWords *.o core

