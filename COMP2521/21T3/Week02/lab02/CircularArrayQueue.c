// Implementation of the Queue ADT using a circular array

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

#include "Queue.h"

#define DEFAULT_SIZE 16 // DO NOT change this line

// DO NOT modify this struct
struct queue {
	Item *items;
	int size;
	int capacity;
	int frontIndex;
};

static void increaseCapacity(Queue q);

/**
 * Creates a new empty queue
 */
Queue QueueNew(void) {
	Queue q = malloc(sizeof(*q));
	if (q == NULL) {
		fprintf(stderr, "couldn't allocate Queue");
		exit(EXIT_FAILURE);
	}

	q->items = malloc(DEFAULT_SIZE * sizeof(Item));
	if (q->items == NULL) {
		fprintf(stderr, "couldn't allocate Queue");
		exit(EXIT_FAILURE);
	}

	q->size = 0;
	q->capacity = DEFAULT_SIZE;
	q->frontIndex = 0;
	return q;
}

/**
 * Frees all resources associated with the given queue
 */
void QueueFree(Queue q) {
	free(q->items);
	free(q);
}

/**
 * Adds an item to the end of the queue
 */
void QueueEnqueue(Queue q, Item it) {
	// TODO
	// Make sure queue Q exists
	assert(q != NULL);

	//when the array is full, resize the array
	if (q->size == q->capacity) increaseCapacity(q);
	
	// If size plus frontIndex is equal to capacity which means the next item we need to put 
	// it in the first position
	q->items[(q->frontIndex + q->size) % q->capacity] = it;
	q->size++;
}

static void increaseCapacity(Queue q) {
	// Double the size of the array
	q->items = realloc(q->items, 2 * q->capacity * sizeof(Item));
	// Make sure the last action is success
	if (q->items == NULL) {
		fprintf(stderr, "couldn't resize Queue\n");
		exit(EXIT_FAILURE);
	}

	// Put all of the items which are in front of the frontIndex after the array in  order
	for (int loop = 0; loop < q->frontIndex; loop++) {
		q->items[loop + q->capacity] = q->items[loop];
	}
	q->capacity *= 2;
}

/**
 * Removes an item from the front of the queue and returns it
 * Assumes that the queue is not empty
 */
Item QueueDequeue(Queue q) {
	// TODO
	// Make sure queue Q exists
	assert(q != NULL);
	// Make sure the queue is not empty
	assert(q->size != 0);

	// Copy the frontIndex item
	Item it = q->items[q->frontIndex];
	// If the frontIndex is the end of the array, set the frontIndex is 0; 
	q->frontIndex = (q->frontIndex + 1) % q->capacity;
	// Size - 1
	q->size--;

	return it;
}

/**
 * Gets the item at the front of the queue without removing it
 * Assumes that the queue is not empty
 */
Item QueueFront(Queue q) {
	assert(q->size > 0);

	return q->items[q->frontIndex];
}

/**
 * Gets the size of the given queue
 */
int QueueSize(Queue q) {
	return q->size;
}

/**
 * Returns true if the queue is empty, and false otherwise
 */
bool QueueIsEmpty(Queue q) {
	return q->size == 0;
}

/**
 * Prints the queue to the given file with items space-separated
 */
void QueueDump(Queue q, FILE *fp) {
	for (int i = q->frontIndex, j = 0; j < q->size; i = (i + 1) % q->capacity, j++) {
		fprintf(fp, "%d ", q->items[i]);
	}
	fprintf(fp, "\n");
}

/**
 * Prints out information for debugging
 */
void QueueDebugPrint(Queue q) {

}

