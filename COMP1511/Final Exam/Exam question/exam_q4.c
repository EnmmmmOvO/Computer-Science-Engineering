#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

struct node {
    struct node *next;
    int          data;
};

struct node *insert_middle(int value, struct node *head);
struct node *create_node(int data, struct node *next);
struct node *strings_to_list(int len, char *strings[]);
void print_list(struct node *head);

// Insert a new node in the middle of the list.
//  - If the list has an even number of nodes, insert the node such that
//    there are an equal number of nodes before and after it.
//  - If the list has an odd number of nodes, insert the node such that
//    there is one more node *before* the inserted node than there is after.
struct node *insert_middle(int value, struct node *head) {
    // TODO: Change this function.

    return NULL;
}



int main(int argc, char *argv[]) {
    int value;
    scanf("%d", &value);
    // create linked list from command line arguments
    struct node *head = NULL;
    if (argc > 1) {
        // list has elements
        head = strings_to_list(argc - 1, &argv[1]);
    }

    struct node *new_head = insert_middle(value, head);
    print_list(new_head);

    return 0;
}


// create linked list from array of strings
struct node *strings_to_list(int len, char *strings[]) {
    struct node *head = NULL;
    int i = len - 1;
    while (i >= 0) {
        struct node *n = malloc(sizeof (struct node));
        assert(n != NULL);
        n->next = head;
        n->data = atoi(strings[i]);
        head = n;
        i -= 1;
    }   
    return head;
}

// print linked list
void print_list(struct node *head) {
    printf("[");    
    struct node *n = head;
    while (n != NULL) {
        // If you're getting an error here,
        // you have returned an invalid list
        printf("%d", n->data);
        if (n->next != NULL) {
            printf(", ");
        }
        n = n->next;
    }
    printf("]\n");
}
