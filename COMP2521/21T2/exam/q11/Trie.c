// Trie

#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "Trie.h"

// Returns a new trie node (initialized to NULLs)
Trie TrieNew(void) {
    Trie node = malloc(sizeof(struct TrieNode));
    node->isEndOfWord = false;
    for (int i = 0; i < ALPHABET_SIZE; i++) {
        node->children[i] = NULL;
    }
    return node;
}

// Inserts a word into the given trie
void TrieInsert(Trie node, char *key) {
    int len = strlen(key);
    assert(len > 0 && len <= MAXWORD);
    for (int level = 0; level < len; level++) {
        int index = (int)(key[level] - 'a');
        if (node->children[index] == NULL) {
            node->children[index] = TrieNew();
        }
        node = node->children[index];
    }
    node->isEndOfWord = true;
}

// Returns true if the given word exists in the trie, and false
// otherwise
bool TrieSearch(Trie node, char *key) {
    int len = strlen(key);
    for (int level = 0; level < len; level++) {
        int index = (int)(key[level] - 'a');
        if (node->children[index] == NULL) {
            return false;
        }
        node = node->children[index];
    }
    return node->isEndOfWord;
}

// Frees all memory associated with the given trie
void TrieFree(Trie root) {
    for (int i = 0; i < ALPHABET_SIZE; i++) {
        if (root->children[i] != NULL) {
            TrieFree(root->children[i]);
        }
    }
    free(root);
}

