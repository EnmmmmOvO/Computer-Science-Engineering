// Implementation of the String List ADT

// !!! DO NOT MODIFY THIS FILE !!!

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "List.h"

typedef struct node *Node;
struct node {
    char  *s;
    Node   next;
};

struct list {
    Node   head;
    Node   tail;
    int    size;
};

static Node newNode(char *s);
static char *myStrdup(char *s);
static int qsortStrcmp(const void *ptr1, const void *ptr2);

////////////////////////////////////////////////////////////////////////

// Creates a new empty list
List ListNew(void) {
    List l = malloc(sizeof(*l));
    if (l == NULL) {
        fprintf(stderr, "error: out of memory\n");
        exit(EXIT_FAILURE);
    }

    l->head = NULL;
    l->tail = NULL;
    l->size = 0;
    return l;
}

// Frees all memory allocated for the given list
void ListFree(List l) {
    Node curr = l->head;
    while (curr != NULL) {
        Node temp = curr;
        curr = curr->next;
        free(temp->s);
        free(temp);
    }
    free(l);
}

// Adds a string to the end of the list
void ListAppend(List l, char *s) {
    Node n = newNode(s);
    if (l->head == NULL) {
        l->head = n;
    } else {
        l->tail->next = n;
    }
    l->tail = n;
    l->size++;
}

static Node newNode(char *s) {
    Node n = malloc(sizeof(*n));
    if (n == NULL) {
        fprintf(stderr, "error: out of memory\n");
        exit(EXIT_FAILURE);
    }
    
    n->s = myStrdup(s);
    n->next = NULL;
    return n;
}

static char *myStrdup(char *s) {
    char *copy = malloc((strlen(s) + 1) * sizeof(char));
    if (copy == NULL) {
        fprintf(stderr, "error: out of memory\n");
        exit(EXIT_FAILURE);
    }
    return strcpy(copy, s);
}

// Returns the number of items in the list
int  ListSize(List l) {
    return l->size;
}

// Sorts the list in ASCII order
void ListSort(List l) {
    char **items = malloc(l->size * sizeof(char *));
    if (items == NULL) {
        fprintf(stderr, "error: out of memory\n");
        exit(EXIT_FAILURE);
    }
    int i = 0;
    for (Node curr = l->head; curr != NULL; curr = curr->next) {
        items[i++] = curr->s;
    }
    qsort(items, l->size, sizeof(char *), qsortStrcmp);
    i = 0;
    for (Node curr = l->head; curr != NULL; curr = curr->next) {
        curr->s = items[i++];
    }
    free(items);
}

static int qsortStrcmp(const void *ptr1, const void *ptr2) {
    char *s1 = *(char **)ptr1;
    char *s2 = *(char **)ptr2;
    return strcmp(s1, s2);
}

// Prints the list, one string per line
// If the strings themselves contain newlines, too bad
void ListPrint(List l) {
    for (Node n = l->head; n != NULL; n = n->next) {
        printf("%s\n", n->s);
    }
}

////////////////////////////////////////////////////////////////////////

struct listIterator {
    Node curr;
    List list;
};

// Creates an iterator for the given list
ListIterator ListItNew(List l) {
    ListIterator it = malloc(sizeof(*it));
    if (it == NULL) {
        fprintf(stderr, "error: out of memory\n");
        exit(EXIT_FAILURE);
    }

    it->curr = l->head;
    it->list = l;
    return it;
}

// Gets the next item in the list. The item should not be modified.
char *ListItNext(ListIterator it) {
    if (it->curr == NULL) {
        fprintf(stderr, "error: no more items in iterator!\n");
        exit(EXIT_FAILURE);
    }

    char *item = it->curr->s;
    it->curr = it->curr->next;
    return item;
}

// Checks if the list has a next item
bool ListItHasNext(ListIterator it) {
    return it->curr != NULL;
}

// Frees the given iterator
void ListItFree(ListIterator it) {
    free(it);
}

