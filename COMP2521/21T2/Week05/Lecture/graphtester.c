// Graph ADT tester ... COMP2521 
#include "Graph.h"
#include <stdio.h>

#define NODES 5

int main(void) {
   Graph g = GraphNew(NODES);
   Edge e;

   e.v = 0; e.w = 4;
   GraphEdgeInsert(g, e);
   e.v = 1; e.w = 3;
   GraphEdgeInsert(g, e);
   e.v = 3; e.w = 1;
   GraphEdgeInsert(g, e);
   e.v = 3; e.w = 4;
   GraphEdgeInsert(g, e);
   GraphShow(g);

   putchar('\n');

   e.v = 1; e.w = 3;
   GraphEdgeRemove(g, e);
   e.v = 4; e.w = 0;
   GraphEdgeRemove(g, e);
   e.v = 4; e.w = 1;
   GraphEdgeRemove(g, e);
   GraphShow(g);
   GraphDestroy(g);

   return 0;
}