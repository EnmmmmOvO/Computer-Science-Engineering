// COMP2521 21T2 Assignment 1
// Dict.h ... interface to the Dictionary ADT
// Stores words and their occurrence counts

// !!! DO NOT MODIFY THIS FILE !!!

#ifndef DICT_H
#define DICT_H

#include "WFreq.h"

typedef struct DictRep *Dict;

// Creates a new Dictionary
Dict DictNew(void);

// Frees the given Dictionary
void DictFree(Dict d);

// Inserts an occurrence of the given word into the Dictionary
void DictInsert(Dict d, char *word);

// Returns the occurrence count of the given word - this should be equal
// to the number of times DictInsert has been called with the same word.
// Returns 0 if the word is not in the Dictionary.
int DictFind(Dict d, char *word);

// Finds  the top `n` frequently occurring words in the given Dictionary
// and stores them in the given  `wfs`  array  in  decreasing  order  of
// frequency,  and then in increasing lexicographic order for words with
// the same frequency. Returns the number of WFreq's stored in the given
// array (this will be min(`n`, #words in the Dictionary)) in  case  the
// Dictionary  does  not  contain enough words to fill the entire array.
// Assumes that the `wfs` array has size `n`.
int DictFindTopN(Dict d, WFreq *wfs, int n);

// Displays the given Dictionary. This is purely for debugging purposes,
// so  you  may  display the Dictionary in any format you want.  You may
// choose not to implement this.
void DictShow(Dict d);

#endif

