# COMP2521 ... Lab 04 Makefile

# !!! DO NOT MODIFY THIS FILE !!!

CC = gcc
CFLAGS = -Wall -Werror -Wno-unused-function -Wno-char-subscripts -g

COMMON = StudentDb.c Tree.c List.c Record.c

.PHONY: all
all: test runDb

test: test.c $(COMMON)
	$(CC) $(CFLAGS) -o test test.c $(COMMON)

runDb: runDb.c $(COMMON)
	$(CC) $(CFLAGS) -o runDb runDb.c $(COMMON)

clean:
	rm -f test runDb
