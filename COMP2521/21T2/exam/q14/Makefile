# COMP2521 Final Exam
# rankPopularity

CC = gcc
CFLAGS = -Wall -Werror -g

all: testRankPopularity

testRankPopularity: testRankPopularity.o rankPopularity.o Graph.o
	$(CC) $(CFLAGS) -o testRankPopularity testRankPopularity.o rankPopularity.o Graph.o

testRankPopularity.o: testRankPopularity.c Graph.h
rankPopularity.o: rankPopularity.c Graph.h
Graph.o: Graph.c Graph.h

clean:
	rm -f testRankPopularity *.o core

