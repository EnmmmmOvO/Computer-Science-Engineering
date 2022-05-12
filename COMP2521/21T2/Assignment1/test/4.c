// COMP2521 21T2 Assignment 1
// Dict.c ... implementation of the Dictionary ADT

#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct DictRep *Dict;

Dict DictNew(void);
Dict DictInsertNew(char *word, int i);
void DictFree(Dict d);
void DictInsert(Dict d, char *word);
Dict Insert(Dict d, char *word, int i);
int compare(Dict d, char *word);
int DictFind(Dict d, char *word);
void search(Dict d);
int DictFindTopN(Dict d, int n);



// you may define your own structs here


struct DictRep {
	// add fields to this struct
	// you can add whatever fields you want
	char *w;
	int freq;
	int height;
	Dict left;
	Dict right;	
};

// add function prototypes for your helper functions here

// Creates a new Dictionary
Dict DictNew(void) {
	Dict d = malloc(sizeof(*d));
	if (d == NULL) {
		fprintf(stderr, "couldn't allocate Queue\n");
		exit(EXIT_FAILURE);
	}
	d->w = NULL;
	d->left = NULL;
	d->right = NULL;
	d->height = 0;
	d->freq = 0;
	return d;
}

// Creates a new Dict
Dict DictInsertNew(char *word, int i) {
	Dict d = DictNew();
	d->w = word;
	d->height = i;
	d->freq = 1;
	return d;
}

// Frees the given Dictionary
void DictFree(Dict d) {
	if (d != NULL) {
		DictFree(d->left);
		DictFree(d->right);
		free(d);
	}
}

// Inserts an occurrence of the given word into the Dictionary
void DictInsert(Dict d, char *word) {
	if (strlen(word) != 0) {
		if (d->w != NULL) {
			Dict dic = d;
			dic = Insert(dic, word, 0);
		} else {
			d->w = word;
			d->freq ++;
		}
	}
}

Dict Insert(Dict d, char *word, int i) {
	if (d == NULL) {
		return DictInsertNew(word, i);
	} else if (compare(d, word) == 0) {
		d->freq ++;
		return d;
	} else if (compare(d, word) == 1) {
		d->right = Insert(d->right, word, i + 1);
	} else if (compare(d, word) == 2) {
		d->left = Insert(d->left, word, i + 1);
	} 
	return d;
}

int compare(Dict d, char *word) {
	for (int i = 0; word[i] != '\0'; i ++) {
		if (d->w[i] == word[i]) {
			if (d->w == word) return 0;
		} else if (d->w[i] < word[i]) {
			return 1;
		} else if (d->w[i] > word[i]) {
			return 2;
		}
	}
	return 2;
}
// Returns the occurrence count of the given word. Returns 0 if the word
// is not in the Dictionary.
int DictFind(Dict d, char *word) {
	if (d == NULL) {
		return 0;
	} else if (compare(d, word) == 0) {
		return d->freq;
	} else if (compare(d, word) == 1) {
		return DictFind(d->right, word);
	} else if (compare(d, word) == 2) {
		return DictFind(d->left, word);
	} 
	return 0;
} 

// Finds  the top `n` frequently occurring words in the given Dictionary
// and stores them in the given  `wfs`  array  in  decreasing  order  of
// frequency,  and then in increasing lexicographic order for words with
// the same frequency. Returns the number of WFreq's stored in the given
// array (this will be min(`n`, #words in the Dictionary)) in  case  the
// Dictionary  does  not  contain enough words to fill the entire array.
// Assumes that the `wfs` array has size `n`.
int DictFindTopN(Dict d, WFreq *wfs, int n) {
	
	return 0;
}

void search(Dict d, WFreq *wfs, int n) {
	if (d == NULL) {
		return;
	}
	search(d->right, wfs, n);
	InsertWFreq(d, Wfreq, n)
	search(d->left, wfs, n);
}

void insertWFreq(Dict d, WFreq *wfs, int n) {
	if ()
}
// Finds  the top `n` frequently occurring words in the given Dictionary
// and stores them in the given  `wfs`  array  in  decreasing  order  of
// frequency,  and then in increasing lexicographic order for words with
// the same frequency. Returns the "rufus" of WFreq's stored in the given
// array (this will be min(`n`, #words in the Dictionary)) in  case  the
// Dictionary  does  not  contain enough words to fill the entire array.
// Assumes that the `wfs` array has size `n`.
/*int DictFindTopN(Dict d, WFreq *wfj, int n) {
	return 0;
}*/
// Displays the given Dictionary. This is purely for debugging purposes,
// so  you  may  display the Dictionary in any format you want.  You may
// choose not to implement this.
int main (void) {
	Dict d = DictNew();
	DictInsert(d, "50");
	DictInsert(d, "40");
	DictInsert(d, "44");
	DictInsert(d, "39");
	DictInsert(d, "88");
	DictInsert(d, "47");
	DictInsert(d, "86");
	DictInsert(d, "10");
	DictInsert(d, "99");
	DictInsert(d, "57");

	printf("%d\n", DictFindTopN(d, 6));
	return 0;
}

