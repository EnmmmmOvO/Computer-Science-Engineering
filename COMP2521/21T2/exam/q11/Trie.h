// Trie

#ifndef TRIE_H
#define TRIE_H

#include <stdbool.h>

#define ALPHABET_SIZE 26

#define MAXWORD 64

typedef struct TrieNode *Trie;

struct TrieNode {
    Trie children[ALPHABET_SIZE]; // index 0 corresponds to 'a',
                                  // index 1 corresponds to 'b', etc.
    bool isEndOfWord;
};

// Returns a new trie node (initialized to NULLs)
Trie TrieNew(void); 

// Inserts a word into the given trie
void TrieInsert(Trie root, char *key);

// Returns true if the given word exists in the trie, and false
// otherwise
bool TrieSearch(Trie root, char *key);

// Frees all memory associated with the given trie
void TrieFree(Trie root);

#endif

