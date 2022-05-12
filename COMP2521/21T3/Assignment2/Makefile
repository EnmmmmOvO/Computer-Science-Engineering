# COMP2521 Assignment 2 Makefile
#
# HOW TO USE
# 1. Ensure that your directory structure looks like:
#    ass2/
#        ex1/
#            collection.txt
#            invertedIndex.txt
#            ...
#        ex2/
#            collection.txt
#            invertedIndex.txt
#            ...
#        ex3/
#            collection.txt
#            invertedIndex.txt
#            ...
#        Makefile (this Makefile)
#        pagerank.c
#        searchPagerank.c
#        scaledFootrule.c
#        Your supporting files...
#
# 2. Read all the comments below and edit the Makefile accordingly
#
# 3. After you use the make command, this will create executables in
#    the ex1, ex2 and ex3 directories. Change into these directories
#    and run your programs (e.g., ./pagerank)

CC = gcc
CFLAGS = -Wall -Werror -g

# Notes:
# Your pagerank.c should have the main() function for Part 1
# Your searchPagerank.c should have the main() function for Part 2
# Your scaledFootrule.c should have the main() function for Part 3
# List all your C files that DON'T contain a main() function here
# For example: SUPPORTING_FILES = hello.c world.c
SUPPORTING_FILES = 

.PHONY: all
all: pagerank searchPagerank scaledFootrule

pagerank: pagerank.c $(SUPPORTING_FILES)
	$(CC) $(CFLAGS) -o pagerank pagerank.c $(SUPPORTING_FILES) -lm
	cp pagerank ex1
	cp pagerank ex2
	cp pagerank ex3

searchPagerank: searchPagerank.c $(SUPPORTING_FILES)
	$(CC) $(CFLAGS) -o searchPagerank searchPagerank.c $(SUPPORTING_FILES) -lm
	cp searchPagerank ex1
	cp searchPagerank ex2
	cp searchPagerank ex3

scaledFootrule: scaledFootrule.c $(SUPPORTING_FILES)
	$(CC) $(CFLAGS) -o scaledFootrule scaledFootrule.c $(SUPPORTING_FILES) -lm
	cp scaledFootrule ex1
	cp scaledFootrule ex2
	cp scaledFootrule ex3

.PHONY: clean
clean:
	rm pagerank searchPagerank scaledFootrule
	rm -f ex?/pagerank ex?/searchPagerank ex?/scaledFootrule

