# COMP2521 Assignment 1

# !!! DO NOT MODIFY THIS FILE !!!

CC = gcc
CFLAGS = -Wall -Werror -g -Wno-unused-function

all: testFs testFsColored mimFs

testFs: testFs.c Fs.c utility.c utility.h listFile.c
	$(CC) $(CFLAGS) -o testFs testFs.c Fs.c utility.c listFile.c

testFsColored: testFs.c Fs.c utility.c utility.h listFile.c
	$(CC) $(CFLAGS) -DCOLORED -o testFsColored testFs.c Fs.c utility.c listFile.c

mimFs: mimFs.c Fs.c utility.c utility.h listFile.c
	$(CC) $(CFLAGS) -DCOLORED -o mimFs mimFs.c Fs.c utility.c listFile.c

clean:
	rm -f testFs testFsColored mimFs

