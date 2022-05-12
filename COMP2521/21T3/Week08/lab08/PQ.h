// Priority queue of edges
// Edges with smaller weight have higher priority

// !!! DO NOT MODIFY THIS FILE !!!

#ifndef PQ_H
#define PQ_H

#include <stdbool.h>

#include "Graph.h"

typedef struct PQRep *PQ;

/**
 * Creates a new priority queue
 * Complexity: O(1)
 */
PQ   PQNew(void);

/**
 * Frees all memory associated with the given priority queue
 * Complexity: O(1)
 */
void PQFree(PQ pq);

/**
 * Adds an edge to the priority queue
 * Average complexity: O(log n)
 */
void PQInsert(PQ pq, Edge e);

/**
 * Removes and returns the edge with the smallest weight from the
 * priority queue. If multiple edges have the same smallest weight, one
 * of them will be removed.
 * Complexity: O(log n)
 */
Edge PQExtract(PQ pq);

/**
 * Returns true if the given priority queue is empty, or false otherwise
 * Complexity: O(1)
 */
bool PQIsEmpty(PQ pq);

/**
 * Prints the given priority queue to stdout for debugging purposes
 */
void PQShow(PQ pq);

#endif
