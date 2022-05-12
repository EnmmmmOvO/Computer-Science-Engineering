# COMP2521 21T2 Assignment 1

# !!! DO NOT MODIFY THIS FILE !!!

CC = gcc
CFLAGS = -Wall -Werror -g

all: tw

tw: tw.o Dict.o stemmer.o

tw.o: tw.c Dict.h WFreq.h stemmer.h 
Dict.o: Dict.c Dict.h WFreq.h
stemmer.o: stemmer.c

clean:
	rm -f tw *.o core

