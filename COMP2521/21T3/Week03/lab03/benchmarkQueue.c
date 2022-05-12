
#include <stdio.h>
#include <stdlib.h>

#include "Queue.h"

int main(void) {
	Queue q = QueueNew();

	// TODO
	// Write a benchmark test to demonstrate the difference between
	// ArrayQueue and CircularArrayQueue	
	for (int loop = 1; loop <= 100000; loop++) 
		QueueEnqueue(q, loop);

	for (int loop = 1; loop <= 100000; loop++) 
		QueueDequeue(q);

	QueueFree(q);
}

