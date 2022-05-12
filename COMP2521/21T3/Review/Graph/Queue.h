#ifndef QUEUE_H
# define QUEUE_H


#include <stdbool.h>

typedef struct queue *Queue;

Queue QueueNew(void);

void QueueFree(Queue q);

void QueueEnqueue(Queue, int);

int QueueDequeue(Queue);

int QueueFront(Queue);

int QueueSize(Queue);

bool QueueIsEmpty(Queue);

#endif