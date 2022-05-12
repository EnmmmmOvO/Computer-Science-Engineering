// printWords.c ... implementation of printWords function

#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "Trie.h"

void printWords(Trie t) {
    if (t != NULL) {

        for (int loop = 0; loop < ALPHABET_SIZE; loop++) {
            if (t->children[loop] != NULL) {
                printf("%c", loop + 'a');
            }
            printWords(t->children[loop]);
        }
        if (t->isEndOfWord == 1){
            printf("\n");
        }
    }
}

