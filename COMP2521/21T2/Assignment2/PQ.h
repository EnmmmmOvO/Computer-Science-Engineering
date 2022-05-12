// Interface for a priority queue ADT
// This priority queue stores items of type int and uses priority values
// of type int, with smaller values having higher priority.
// COMP2521 Assignment 2

// !!! DO NOT MODIFY THIS FILE !!!

#ifndef PQ_H
#define PQ_H

#include <stdbool.h>

typedef struct PQRep *PQ;

/**
 * Creates a new priority queue
 */
PQ   PQNew(void);

/**
 * Adds  an item with the given priority value to the priority queue. If
 * the item already exists, its priority value is updated to  the  given
 * priority  value. The update is treated as if the item was removed and
 * then reinserted.
 */
void PQInsert(PQ pq, int item, int priority);

/**
 * Removes  and  returns  the item with the smallest priority value from
 * the priority queue. If multiple items have the same  priority  value,
 * the  item  which  was  inserted  the  earliest  out  of those will be
 * removed.
 */
int  PQDequeue(PQ pq);

/**
 * Updates  the  priority  value of an item in the priority queue to the
 * given priority value. If there is no such item in the priority queue,
 * no  action is taken. The update is treated as if the item was removed
 * and then reinserted.
 */
void PQUpdate(PQ pq, int item, int priority);

/**
 * Returns true if the given priority queue is empty, or false otherwise
 */
bool PQIsEmpty(PQ pq);

/**
 * Prints the given priority queue to stdout for debugging purposes
 */
void PQShow(PQ pq);

/**
 * Frees all memory associated with the given priority queue
 */
void PQFree(PQ pq);

#endif

