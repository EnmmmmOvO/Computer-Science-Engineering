// Linked list interface ... COMP2521 
#include <stdbool.h>

typedef struct Node *List;

List insertLL(List, int);
List deleteLL(List, int);
bool inLL(List, int);
void freeLL(List);
void showLL(List);