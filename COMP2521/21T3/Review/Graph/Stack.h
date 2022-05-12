#ifndef STACK_H
#define STACK_H

#include <stdbool.h>

typedef struct stack *Stack;

Stack StackNew(void);

void StackFree(Stack q);

void StackEnstack(Stack, int);

int StackDestack(Stack);

int StackFront(Stack);

int StackSize(Stack);

bool StackIsEmpty(Stack);

#endif