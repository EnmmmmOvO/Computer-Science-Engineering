// testTriePrintWords.c

#include <stdio.h>
#include <stdlib.h>

#include "Trie.h"

#define MAXLINE 1024

void printWords(Trie t);

int main(void) {
    Trie root = TrieNew();
    char s[MAXLINE];

    while (scanf("%s", s) == 1) {
        TrieInsert(root, s);
    }

    printWords(root);
    TrieFree(root);
}

