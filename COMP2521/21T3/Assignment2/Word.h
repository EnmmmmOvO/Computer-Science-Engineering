

#ifndef WORD_H
#define WORD_H

#include <stdbool.h>

#define MAX_SIZE 100

typedef struct url *Url;
typedef struct word *Word;
typedef struct graph *Graph;



Graph GraphNew();

Url urlNew(char *code, double w);

void inputUrl(Graph g, char *code, double w);

void inputLine(Graph g, char *line);

void search(Graph g, char *c);

void print(Graph g);

#endif
