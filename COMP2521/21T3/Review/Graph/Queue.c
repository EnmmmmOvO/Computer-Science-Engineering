#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

#include "Queue.h"

typedef struct node *Node;

struct node {
    int data;
    Node next;
};

struct queue {
    int num;
    Node head;
    Node tail;
};

Queue QueueNew(void) {
    Queue q = malloc(sizeof(Queue));
    assert(q != NULL);
    q->head = NULL;
    q->tail = NULL;
    q->num = 0;
    return q;
}

Node NodeNew(int value) {
    Node n = malloc(sizeof(Node));
    assert(n != NULL);
    n->data = value;
    n->next = NULL;
    return n;
}

void QueueFree(Queue q) {
    for (int i = 0; i < q->num; i++, q->head = q->head->next) {
        free(q->head);
    }
    free(q);
}

void QueueEnqueue(Queue q, int value) {
    if (q->num == 0) {
        q->head = NodeNew(value);
        q->tail = q->head;
    } else {
        q->tail->next = NodeNew(value);
        q->tail = q->tail->next;
    }
    q->num++;
}

int QueueDequeue(Queue q) {
    int temp = q->head->data;
    Node tempNode = q->head;
    q->head = q->head->next;
    q->num--;
    free(tempNode);
    return temp;
}

int QueueFront(Queue q) {
    return q->head->data;
}

int QueueSize(Queue q) {
    return q->num;
}

bool QueueIsEmpty(Queue q) {
    return q->num == 0;
}



