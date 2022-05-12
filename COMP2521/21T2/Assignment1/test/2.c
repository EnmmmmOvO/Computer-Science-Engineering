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
Dict AVL(Dict d, char *word);
Dict rotateLeft(Dict d);
int getDepth(Dict d);
int GetHeight(Dict t);
void change(Dict p, Dict d, Dict q);
Dict rotateRight(Dict d);


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
	d->height = 0;
	d->right = NULL;
	d->freq = 0;
	return d;
}

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
			Dict p = Insert(d, word, 0);
			if (d != p) {
				char *a = d->w;
				d->w = p->w;
				p->w = a;

				int temp = d->freq;
				d->freq = p->freq;
				p->freq = temp;

			 	Dict tempL = d->left;
				d->left = p->left;
				p->left = tempL;
				
				Dict tempR = d->right;
				d->right = p->right;
				p->right = tempR;

				change(p, d, p);
			}
		} else {
			d->w = word;
			d->freq ++;
		}
	}
}

void change(Dict p, Dict d, Dict q) {
	if (q == NULL) {
		return;
	}
	change(p, d, q->left);
	change(p, d, q->right);
	if (q->left == d) {
		q->left = p;
		return;
	}
	if (q->right == d) {
		q->right = p;
		return;
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
	return AVL(d, word);
}

Dict AVL(Dict d, char *word) {
	if (d == NULL) {
		return d;
	}
	d->left = AVL(d->left, word);
	d->right = AVL(d->right, word);
	int sub = getDepth(d->left) - getDepth(d->right);

    if (sub > 1) {
        if (compare(d->left, word) == 1) 
			d->left = rotateLeft(d->left);
		d = rotateRight(d);
	} else if (sub < -1) {
        if (compare(d->right, word) == 2) { 
			d->right = rotateRight(d->right);
		}
        d = rotateLeft(d);
	}
	
	return d;
	
}

int getDepth(Dict d)
{
	int  ldepth, rdepth;
	if (d == NULL)  return 0;
	else {
		rdepth = getDepth(d->right);
		ldepth = getDepth(d->left);
		return (rdepth > ldepth) ? (rdepth + 1) : (ldepth + 1);
	}
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

Dict rotateLeft(Dict d) {
	if (d == NULL || d->right == NULL) {
        return d;
    }
	Dict q = d->right;
	d->right = q->left;
	q->left = d;
	d = q;
	return q;
}

Dict rotateRight(Dict d) {
	if (d == NULL || d->left == NULL) {
        return d;
    }
   	Dict q = d->left;
   	d->left = q->right;
   	q->right = d;
	d = q;

	return q;
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
	DictInsert(d, "58");
	DictInsert(d, "26");
	DictInsert(d, "60");
	DictInsert(d, "37");
	DictInsert(d, "58");
	DictInsert(d, "49");
	DictInsert(d, "99");
	DictInsert(d, "34");



	printf("%s %d %d\n",d->w, d->freq, d->height);
	return 0;
}

