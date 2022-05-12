#include <stdio.h>
#include <stdlib.h>

#include "Queue.h"

int main(void) {
	Queue q = QueueNew();
	
	for (int loop = 1; loop <= 100000; loop ++) 
		QueueEnqueue(q, loop);

	for (int loop = 1; loop <= 80000; loop ++) 
		QueueDequeue(q);

	for (int loop = 1; loop <= 120000; loop ++) 
		QueueDequeue(q);

	QueueFree(q);
}

