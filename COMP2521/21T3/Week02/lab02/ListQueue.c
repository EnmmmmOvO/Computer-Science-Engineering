// Implementation of the Queue ADT using a linked list

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

#include "Queue.h"

typedef struct node *Node;
struct node {
	Item item;
	Node next;
};

struct queue {
	Node head;
	Node tail;
	int  size;
};

/**
 * Creates a new empty queue
 */
Queue QueueNew(void) {
	Queue q = malloc(sizeof(*q));
	if (q == NULL) {
		fprintf(stderr, "couldn't allocate Queue\n");
		exit(EXIT_FAILURE);
	}

	q->head = NULL;
	q->tail = NULL;
	q->size = 0;
	return q;
}

/**
 * Frees all resources associated with the given queue
 */
void QueueFree(Queue q) {
	Node curr = q->head;
	while (curr != NULL) {
		Node temp = curr;
		curr = curr->next;
		free(temp);
	}
	free(q);
}

/**
 * Adds an item to the end of the queue
 */
void QueueEnqueue(Queue q, Item it) {
	// TODO
	// Make sure queue Q exists
	assert(q != NULL);

	// Create a new node to exist Item it and set the node 
	Node n = malloc(sizeof(Node));
	n->item = it;
	n->next = NULL;

	// Check whether last action is success or not
	if (n == NULL) {
		fprintf(stderr, "couldn't allocate Node\n");
		exit(EXIT_FAILURE);
	}

	// If the Queue q is empty, set head and tail node
	if (q->size == 0) {
		q->head = n;
	} else {
		q->tail->next = n;
	}

	// Put the new node address in tail->next and set n to the new tail
	q->tail = n;
	q->size++;
}

/**
 * Removes an item from the front of the queue and returns it
 * Assumes that the queue is not empty
 */
Item QueueDequeue(Queue q) {
	// TODO
	// Make sure queue Q exists
	assert(q != NULL);
	// Make sure the queue q is not empty
	assert(q->size != 0);
	
	// Copy the head node
	Node n = q->head;
	// Setthe next node to the new head
	q->head = n->next;
	q->size--;
	// copy the item of head node
	Item i = n->item;
	// free the head node
	free(n);
	// return item
	return i;
}

/**
 * Gets the item at the front of the queue without removing it
 * Assumes that the queue is not empty
 */
Item QueueFront(Queue q) {
	assert(q->size > 0);

	return q->head->item;
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
	for (Node curr = q->head; curr != NULL; curr = curr->next) {
		fprintf(fp, "%d ", curr->item);
	}
	fprintf(fp, "\n");
}

/**
 * Prints out information for debugging
 */
void QueueDebugPrint(Queue q) {
	
}

