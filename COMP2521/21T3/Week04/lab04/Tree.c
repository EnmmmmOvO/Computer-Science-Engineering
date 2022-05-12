// Implementation of the Record Tree ADT

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

#include "List.h"
#include "Record.h"
#include "Tree.h"

typedef struct node *Node;
struct node {
    Record rec;
    Node   left;
    Node   right;
};

struct tree {
    Node    root;
    int     (*compare)(Record, Record);
};

////////////////////////////////////////////////////////////////////////
// Auxiliary functions

static void doTreeFree(Node n, bool freeRecords);
static Node doTreeInsert(Tree t, Node n, Record rec, bool *res);
static Node newNode(Record rec);
static Node doTreeDelete(Tree t, Node n, Record rec, bool *res);
static Node joinTrees(Node t1, Node t2);
static Record doTreeSearch(Tree t, Node n, Record rec);
static void doTreeSearchBetween(Tree t, Node n, Record lower,
                                Record upper, List l);
static void doTreeListInOrder(Node n);

////////////////////////////////////////////////////////////////////////

Tree TreeNew(int (*compare)(Record, Record)) {
    Tree t = malloc(sizeof(*t));
    if (t == NULL) {
        fprintf(stderr, "error: out of memory\n");
        exit(EXIT_FAILURE);
    }

    t->root = NULL;
    t->compare = compare;
    return t;
}

////////////////////////////////////////////////////////////////////////

void TreeFree(Tree t, bool freeRecords) {
    doTreeFree(t->root, freeRecords);
    free(t);
}

static void doTreeFree(Node n, bool freeRecords) {
    if (n != NULL) {
        doTreeFree(n->left, freeRecords);
        doTreeFree(n->right, freeRecords);
        if (freeRecords) {
            RecordFree(n->rec);
        }
        free(n);
    }
}

////////////////////////////////////////////////////////////////////////

bool TreeInsert(Tree t, Record rec) {
    bool res = false; // if the record was inserted
    t->root = doTreeInsert(t, t->root, rec, &res);
    return res;
}

static Node doTreeInsert(Tree t, Node n, Record rec, bool *res) {
    if (n == NULL) {
        *res = true;
        return newNode(rec);
    }

    int cmp = t->compare(rec, n->rec);
    if (cmp < 0) {
        n->left = doTreeInsert(t, n->left, rec, res);
    } else if (cmp > 0) {
        n->right = doTreeInsert(t, n->right, rec, res);
    } else {
        *res = false;
    }
    return n;
}

static Node newNode(Record rec) {
    Node n = malloc(sizeof(*n));
    if (n == NULL) {
        fprintf(stderr, "error: out of memory\n");
        exit(EXIT_FAILURE);
    }

    n->left = NULL;
    n->right = NULL;
    n->rec = rec;
    return n;
}

////////////////////////////////////////////////////////////////////////

bool TreeDelete(Tree t, Record rec) {
    bool res = false;
    t->root = doTreeDelete(t, t->root, rec, &res);
    return res;
}

static Node doTreeDelete(Tree t, Node n, Record rec, bool *res) {
    if (n == NULL) {
        *res = false;
        return NULL;
    }

    int cmp = t->compare(rec, n->rec);
    if (cmp < 0) {
        n->left = doTreeDelete(t, n->left, rec, res);
    } else if (cmp > 0) {
        n->right = doTreeDelete(t, n->right, rec, res);
    } else {
        *res = true;
        Node l = n->left;
        Node r = n->right;
        free(n);
        n = joinTrees(l, r);
    }

    return n;
}

static Node joinTrees(Node t1, Node t2) {
    if (t1 == NULL) {
        return t2;
    } else if (t2 == NULL) {
        return t1;
    } else {
        Node curr = t2;
        Node prev = NULL;
        while (curr->left != NULL) {
            prev = curr;
            curr = curr->left;
        }

        if (prev != NULL) {
            prev->left = curr->right;
            curr->right = t2;
        }

        curr->left = t1;
        return curr;
    }
}

////////////////////////////////////////////////////////////////////////

Record TreeSearch(Tree t, Record rec) {
    return doTreeSearch(t, t->root, rec);
}

static Record doTreeSearch(Tree t, Node n, Record rec) {
    if (n == NULL) {
        return NULL;
    }

    int cmp = t->compare(rec, n->rec);
    if (cmp < 0) {
        return doTreeSearch(t, n->left, rec);
    } else if (cmp > 0) {
        return doTreeSearch(t, n->right, rec);
    } else {
        return n->rec;
    }
}

////////////////////////////////////////////////////////////////////////

List TreeSearchBetween(Tree t, Record lower, Record upper) {
    // TODO: Complete this function
    Node n = t->root;
    List l = ListNew();

    /*if (t->compare(n->rec, lower) < 0) {
        for (; t->compare(n->rec, lower) < 0 && n->right != NULL; n = n->right);
        if (n->right == NULL && t->compare(n->rec, upper) < 0) return l;
    } else if (t->compare(n->rec, lower) > 0) {
        if (t->compare(n->rec, upper) > 0) return l;
        for (; t->compare(n->rec, lower) > 0 && n->left != NULL; n = n->left);
        if (t->compare(n->rec, lower) != 0) n = n->right;

    }

    for (; t->compare(n->rec, upper) <= 0 && n != NULL; n = n->right) {
        ListAppend(l, n->rec);
        if (n->right == NULL) break;
    }*/
    
    doTreeSearchBetween(t, n, lower, upper, l);
    return l;
}

// n - the current node
// l - a list to accumulate results
static void doTreeSearchBetween(Tree t, Node n, Record lower,
                                Record upper, List l) {
    // TODO: Complete this function
    if (n == NULL) {
        return;
    } else if (t->compare(n->rec, lower) < 0) {
        doTreeSearchBetween(t, n->right, lower, upper, l); 
    } else if (t->compare(n->rec, upper) > 0) {
        doTreeSearchBetween(t, n->left, lower, upper, l);
    } else {
        doTreeSearchBetween(t, n->left, lower, upper, l);
        ListAppend(l, n->rec);
        doTreeSearchBetween(t, n->right, lower, upper, l);
    }
}

////////////////////////////////////////////////////////////////////////

void TreeListInOrder(Tree t) {
    doTreeListInOrder(t->root);
}

static void doTreeListInOrder(Node n) {
    if (n != NULL) {
        doTreeListInOrder(n->left);
        RecordShow(n->rec);
        printf("\n");
        doTreeListInOrder(n->right);
    }
}
