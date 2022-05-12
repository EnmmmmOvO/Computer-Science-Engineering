
#ifndef GRAPH_H
#define GRAPH_H

#include <stdbool.h>

#define MAX_SIZE 100

typedef struct url *Url;
typedef struct graph *Graph;



Graph GraphNew();

Url UrlNew(char c[MAX_SIZE]);

void GraphFree(Graph g);

////////////////////////////////////////////////////////////////////////
void GraphUrlInsert(Graph g, char code[MAX_SIZE]);

char *getUrlCode(Graph g, int loop);

int GraphNumVertices(Graph g);

void UrlLink(Graph g, int loop, char c[MAX_SIZE]);

void UrlContentInsert(Graph g, int loop, char *urlContent);

void setWeight(Graph g, double n);

double changeWeight(Graph g, int t, double d);

void print(Graph g);

void printWeight(Graph g, int t) ;

#endif
