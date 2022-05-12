#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

#include "Stack.h"

typedef struct node *Node;

struct node {
    int data;
    Node next;
};

struct stack {
    Node head;
    int num;
};

Stack StackNew(void) {
    Stack s = malloc(sizeof(Stack));
    assert(s != NULL);
    s->head = NULL;
    s->num = 0;
    return s;
}

void StackFree(Stack s) {
    for (int i = 0; i < s->num; i++, s->head = s->head->next) {
        free(s->head);
    }
    free(s);
}

Node NodeNew(int value) {
    Node n = malloc(sizeof(Node));
    assert(n != NULL);
    n->data = value;
    n->next = NULL;
    return n;
}

void StackEnstack(Stack s, int value) {
    if (s->num == 0) {
        s->head = NodeNew(value);
    } else {
        Node temp = NodeNew(value);
        temp->next = s->head;
        s->head = temp;
    }
    s->num++;
}

int StackDestack(Stack s) {
    Node tempNode = s->head;
    int temp = s->head->data;
    s->head = s->head->next;
    s->num--;
    free(tempNode);
    return temp; 
}

int StackFront(Stack s) {
    return s->head->data;
}

int StackSize(Stack s) {
    return s->num;
}

bool StackIsEmpty(Stack s) {
    return s->num == 0;
}