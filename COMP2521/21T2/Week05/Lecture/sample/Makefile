all: 1 2 3

1: graph-array-of-edges.o graphtester.o
	gcc -Wall -Werror -o graph-array-of graph-array-of-edges.o graphtester.o

2: graph-adj-matrix.o graphtester.o
	gcc -Wall -Werror -o graph-adj-matrix graph-adj-matrix.o graphtester.o

3: graph-adj-list.o list.o graphtester.o
	gcc -Wall -Werror -o graph-adj-list graph-adj-list.o list.o graphtester.o

graphtester.o: graphtester.c Graph.h
	gcc -Wall -Werror -c graphtester.c

graph-array-of-edges.o: graph-array-of-edges.c Graph.h
	gcc -Wall -Werror -c graph-array-of-edges.c

graph-adj-matrix.o: graph-adj-matrix.c Graph.h
	gcc -Wall -Werror -c graph-adj-matrix.c

graph-adj-list.o: graph-adj-list.c Graph.h list.h
	gcc -Wall -Werror -c graph-adj-list.c

list.o: list.c list.h
	gcc -Wall -Werror -c list.c

clean:
	rm -f graph-array-of graph-adj-matrix graph-adj-list graphtester.o graph-array-of-edges.o graph-adj-matrix.o graph-adj-list.o list.o