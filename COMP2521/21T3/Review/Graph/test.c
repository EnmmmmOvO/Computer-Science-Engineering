#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>


#include "Stack.h"



int main (void) {
    /*Queue q = QueueNew();
    QueueEnqueue(q, 1);
    QueueEnqueue(q, 2);
    QueueEnqueue(q, 3);
    QueueEnqueue(q, 4);
    printf("DE %d\n", QueueDequeue(q));
    printf("NU %d\n", QueueSize(q));
    printf("FR %d\n", QueueFront(q));
    printf("NU %d\n", QueueSize(q));
    printf("TR %d\n", QueueIsEmpty(q));
    printf("DE %d\n", QueueDequeue(q));
    printf("DE %d\n", QueueDequeue(q));
    printf("DE %d\n", QueueDequeue(q));
    printf("NU %d\n", QueueSize(q));
    printf("TR %d\n", QueueIsEmpty(q));
    QueueFree(q);*/

    Stack s = StackNew();
    StackEnstack(s, 1);
    StackEnstack(s, 2);
    StackEnstack(s, 3);
    StackEnstack(s, 4);
    printf("DE %d\n", StackDestack(s));
    printf("DE %d\n", StackDestack(s));
    printf("DE %d\n", StackDestack(s));
    StackEnstack(s, 4);
    printf("DE %d\n", StackDestack(s));

}