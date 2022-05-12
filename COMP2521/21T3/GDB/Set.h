// Set ADT Interface

#ifndef SET_H
#define SET_H

#include <stdbool.h>

typedef struct set *Set;

/**
 * Creates a new empty set
 */
Set  SetNew(void);

/**
 * Frees all resources associated with the given set
 */
void SetFree(Set s);

/**
 * Adds an element to the given set
 * Does not insert duplicates
 */
void SetAdd(Set s, int elem);

/**
 * Returns true if the given element is contained in the set, and false
 * otherwise
 */
bool SetContains(Set s, int elem);

/**
 * Returns the size (number of elements) of the given set
 */
int  SetSize(Set s);

/**
 * Prints the set to stdout
 */
void SetPrint(Set s);

#endif
