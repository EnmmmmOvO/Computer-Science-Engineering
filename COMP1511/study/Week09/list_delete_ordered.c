#include <stdio.h>
#include <stdlib.h>

// Do not edit this struct. You may use it exactly as
// it is but you cannot make changes to it

// A node in a linked list
struct node {
    int data;
    struct node *next;
};

// ADD ANY FUNCTION DECLARATIONS YOU WISH TO USE HERE

// Remove any nodes in a list that are higher 
// than the node directly after them.
// Return the head of the list.
// The returned list must have no disorder in it!
struct node *remove_disorder(struct node *head) {
    //head = NULL;
    if (head == NULL) 
        return head;

    int length;
    struct node *p = head;
    for (length = 0; p != NULL; p = p->next, length ++);

    if (length == 1) {
        return head;
    } else if (length == 2) {
        p = head;
        if (p->data > p->next->data) {
            head = head->next;
            free(p);
            return head;
        } else {
            return head;
        }
    }

    struct node *q = head;
    struct node *c = head;

    int loop;
    p = head;
    while (p->next != NULL) {
        loop = 0;
        for (q = p->next; q != NULL; q = q->next) {
            if (q->data < p->data) {
                loop = 1;
            }
        }
        if (loop == 1) {
            if (head == p) {
                c = c->next;
                q = head;
                p = p->next;
                head = head->next;
                free(q);
            } else {
                q = p;
                p = p->next;
                c->next = p;
                free(q);
            }
        } else {
            if (p == head) {
                p = p->next;
            } else {
                p = p->next;
                c = c->next;
            }
        }

    }
    
    return head;
}

// These helper functions are for the main below and will
// have no effect on your remove_disorder. They do not
// need to be modified.
struct node *make_list1(int a);
struct node *make_list2(int a, int b);
struct node *make_list(int a, int b, int c);
void printList(struct node *head);

// This is a main function which could be used
// to test your remove_disorder function.
// It will not be marked.
// Only your remove_disorder function will be marked.
//
// It's recommended to change the int values in this
// main to test whether your remove_disorder is working.
int main(void) {
    // test an ordered list
    struct node *ordered = make_list(1, 2, 3);
    ordered = remove_disorder(ordered);
    printList(ordered);
    
    // test removing one element out of order
    ordered = make_list(1, 3, 2);
    ordered = remove_disorder(ordered);
    printList(ordered);
    
    // test a completely disordered list
    ordered = make_list(3, 2, 1);
    ordered = remove_disorder(ordered);
    printList(ordered);

    // test with the first removal causing more disorder
    ordered = make_list(2, 3, 1);
    ordered = remove_disorder(ordered);
    printList(ordered);

    ordered = make_list2(3, 2);
    ordered = remove_disorder(ordered);
    printList(ordered);

    ordered = make_list2(2, 3);
    ordered = remove_disorder(ordered);
    printList(ordered);

    ordered = make_list1(3);
    ordered = remove_disorder(ordered);
    printList(ordered);

    ordered = NULL;
    ordered = remove_disorder(ordered);
    printList(ordered);
        
    return 0;
}

// A simple function to make a linked list with 3 elements
// This function is purely for the main above
// You will be tested with lists that are more and less
// than 3 elements long
struct node *make_list(int a, int b, int c) {
    struct node *head = malloc(sizeof (struct node));
    struct node *n = head;
    n->data = a;
    n->next = malloc(sizeof (struct node));
    n = n->next;
    n->data = b;
    n->next = malloc(sizeof (struct node));
    n = n->next;
    n->data = c;
    n->next = NULL;
    
    return head;
}

void printList(struct node *head) {
    while (head != NULL) {
        printf("%d ", head->data);
        head = head->next;
    }
    printf("\n");
}

struct node *make_list1(int a) {
    struct node *head = malloc(sizeof (struct node));
    struct node *n = head;
    n->data = a;
    n->next = NULL;
    return head;
}

struct node *make_list2(int a, int b) {
    struct node *head = malloc(sizeof (struct node));
    struct node *n = head;
    n->data = a;
    n->next = malloc(sizeof (struct node));
    n = n->next;
    n->data = b;
    n->next = NULL;
    return head;
}
// ADD ANY FUNCTION DEFINITIONS YOU WISH TO USE HERE

