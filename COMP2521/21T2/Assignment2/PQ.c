// Implementation of a priority queue ADT
// COMP2521 Assignment 2

// !!! DO NOT MODIFY THIS FILE !!!

// Note: This priority queue implementation uses a linear array and does
//       not  arrange  the items in any particular order. It is designed
//       to be simple and is therefore inefficient.

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

#include "PQ.h"

#define DEFAULT_SIZE 64

typedef struct item {
	int item;
	int priority;
} ItemPQ;

struct PQRep {
	ItemPQ *items;
	int numItems;
	int capacity;
};

PQ PQNew(void) {
	PQ pq = malloc(sizeof(*pq));
	if (pq == NULL) {
		fprintf(stderr, "Couldn't allocate PQ!\n");
		exit(EXIT_FAILURE);
	}

	pq->items = malloc(DEFAULT_SIZE * sizeof(ItemPQ));
	if (pq == NULL) {
		fprintf(stderr, "Couldn't allocate PQ!\n");
		exit(EXIT_FAILURE);
	}

	pq->numItems = 0;
	pq->capacity = DEFAULT_SIZE;
	return pq;
}

void PQInsert(PQ pq, int item, int priority) {
	assert(pq != NULL);

	// If item is already in the PQ, use updatePQ
	for (int i = 0; i < pq->numItems; i++) {
		if (pq->items[i].item == item) {
			PQUpdate(pq, item, priority);
			return;
		}
	}

	// If the PQ is full, expand it (i.e., double its capacity)
	if (pq->numItems == pq->capacity) {
		pq->capacity *= 2;
		pq->items = realloc(pq->items, pq->capacity * sizeof(ItemPQ));
		if (pq->items == NULL) {
			fprintf(stderr, "Couldn't expand PQ!\n");
			exit(EXIT_FAILURE);
		}
	}

	// Add the new item to the end
	pq->items[pq->numItems] = (ItemPQ) {item, priority};
	pq->numItems++;
}

int PQDequeue(PQ pq) {
	assert(pq != NULL);
	assert(pq->numItems > 0);

	// Find earliest element with smallest value (highest priority)
	int chosenIndex = 0;
	for (int i = 1; i < pq->numItems; i++) {
		if (pq->items[i].priority < pq->items[chosenIndex].priority) {
			chosenIndex = i;
		}
	}

	int item = pq->items[chosenIndex].item;
	// Shuffle down everything after that element
	for (int i = chosenIndex + 1; i < pq->numItems; i++) {
		pq->items[i - 1] = pq->items[i];
	}
	pq->numItems--;

	return item;
}

void PQUpdate(PQ pq, int item, int priority) {
	assert(pq != NULL);

	for (int i = 0; i < pq->numItems; i++) {
		if (pq->items[i].item == item) {
			pq->items[i].priority = priority;

			// Move updated element to the end
			ItemPQ updatedItem = pq->items[i];
			for (int j = i; j < pq->numItems - 1; j++) {
				pq->items[j] = pq->items[j + 1];
			}
			pq->items[pq->numItems - 1] = updatedItem;
			return;
		}
	}
}

bool PQIsEmpty(PQ pq) {
	assert(pq != NULL);

	return (pq->numItems == 0);
}

void PQShow(PQ pq) {
	assert(pq != NULL);

	printf("#items = %d\n", pq->numItems);
	printf("Items:");
	for (int i = 0; i < pq->numItems; i++) {
		printf(" (item: %d, priority: %d)",
		       pq->items[i].item, pq->items[i].priority);
	}
	printf("\n");
}

void PQFree(PQ pq) {
	assert(pq != NULL);

	free(pq->items);
	free(pq);
}

