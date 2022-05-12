# COMP2521 Lab 8 Makefile

CC = gcc
CFLAGS = -Wall -Werror -g

OBJS1 = testGraphMST.o Graph.o PQ.o
OBJS2 = gridPlanner.o Graph.o planner.o PQ.o

all: testGraphMST gridPlanner

testGraphMST: $(OBJS1)
	$(CC) $(CFLAGS) -o testGraphMST $(OBJS1)

gridPlanner: $(OBJS2)
	$(CC) $(CFLAGS) -o gridPlanner $(OBJS2) -lm

testGraphMST.o: testGraphMST.c Graph.h

gridPlanner.o: gridPlanner.c Place.h planner.h

Graph.o: Graph.c Graph.h PQ.h

planner.o: planner.c planner.h Graph.h Place.h PQ.h

PQ.o: PQ.c PQ.h Graph.h

clean:
	rm -f testGraphMST gridPlanner $(OBJS1) $(OBJS2)
