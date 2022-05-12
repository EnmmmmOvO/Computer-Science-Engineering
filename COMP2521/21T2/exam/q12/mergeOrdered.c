// mergeOrdered.c ... implementation of mergeOrdered function

#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

#include "list.h"

List mergeOrdered(List list1, List list2) {
    List new = ListNew();
    Node p = newNode(0);
    new->first = p;
    Node start1 = list1->first;
    Node start2 = list2->first;
    while (start1 != NULL && start2 != NULL) {
        if (start1->value < start2->value || start2 == NULL) {
            Node q = newNode(start1->value);
            p->next = q;
            start1 = start1->next;
            p = p->next;
        } else if (start1->value >= start2->value || start1 == NULL) {
            Node q = newNode(start2->value);
            p->next = q;
            start2 = start2->next;
            p = p->next;
        }
    }
    if (start1 != NULL) {
        while (start1 != NULL) {
            Node q = newNode(start1->value);
            p->next = q;
            start1 = start1->next;
            p = p->next;
        }
    }
    if (start2 != NULL) {
        while (start2 != NULL) {
            Node q = newNode(start2->value);
            p->next = q;
            start2 = start2->next;
            p = p->next;
        }
    }


    Node n = new->first;
    new->first = new->first->next;
    free(n);
    for (n = new->first; n->next != NULL; n = n->next);
    new->last = n;

    return new;
}

