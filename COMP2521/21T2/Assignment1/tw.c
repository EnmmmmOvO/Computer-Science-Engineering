// COMP2521 21T2 Assignment 1
// tw.c ... compute top N most frequent words in file F
// Usage: ./tw [Nwords] File

#include <assert.h>
#include <ctype.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "Dict.h"
#include "stemmer.h"
#include "WFreq.h"

#define MAXLINE 1000
#define MAXWORD 100

#define isWordChar(c) (isalnum(c) || (c) == '\'' || (c) == '-')

int start(char line[MAX_LINE_LENGTH + 1]);
int end(char line[MAX_LINE_LENGTH + 1]);
void Insert_stopwords(FILE *fp1, Dict d);
int word_use_or_not(Dict d, char *word);
// add function prototypes for your own functions here

int main(int argc, char *argv[]) {
	int   nWords;    // number of top frequency words to show
	char *fileName;  // name of file containing book text

	// process command-line args
	switch (argc) {
		case 2:
			nWords = 10;
			fileName = argv[1];
			break;
		case 3:
			nWords = atoi(argv[1]);
			if (nWords < 10) nWords = 10;
			fileName = argv[2];
			break;
		default:
			fprintf(stderr,"Usage: %s [Nwords] File\n", argv[0]);
			exit(EXIT_FAILURE);
	}

	FILE *fp;
	fp = fopen(fileName, "r");

	if (fp == NULL) {
			fprintf(stderr, "Can't open %s\n", fileName);
			exit(EXIT_FAILURE);
		}


	FILE *fp1;
	fp1 = fopen("stopwords", "r");

	if (fp1 == NULL) {
	    fprintf(stderr, "Can't open stopwords\n");
		exit(EXIT_FAILURE);
	}
	Dict stopwords = DictNew();
	Insert_stopwords(FILE *fp1, Dict d);	

	Dict d = DictNew();
	char line[MAXLINE];
	int temp = 0;
	while (fgets(line, MAXLINE + 1, fp) != NULL && temp == 0) {
		
		if (start(line) == 1) temp = 1;
	}

	if (temp == 0)  fprintf(stderr, "Not a Project Gutenberg book\n");
	while (fgets(line, MAX_LINE_LENGTH + 1, fp) != NULL && temp == 1) {
		if (end(line) == 1) temp = 0;
		int start = 0;
		for (int loop = start; line[loop] != '\0'; loop ++) {
			if (!isWordChar(line[loop])) {
                char word[MAXWORD];
                int temp = 0;
				for (int a = start; a < loop; a ++) {
                    word[temp] = tolower(line[a]);
                    temp ++;
                }
                word[temp] = '\0';
                char *find = strchr(word,'\n');
                if (find) *find = '\0';
                
                if (word_use_or_not(word) == 1) {
                    DictInsert(d, word);
                } 
                start = loop + 1;
			}
		}	
	}
	if (temp == 1)  fprintf(stderr, "Not a Project Gutenberg book\n");

	WFreq wfs;
	int num = DictFindTopN(d, wfs, num);
	for (int loop = 0; loop < num; loop ++)
		printf("%s %d\n", wfs->word, wfs->freq);

	DictFree(stopwords);
	DictFree(d);
	return 0;
}


// add your own functions here
int start(char line[MAX_LINE_LENGTH + 1]) {
	if (line[0] == '*' && line[1] == '*' &&
		line[2] == '*' && line[3] == ' ' &&
		line[4] == 'S' && line[1] == 'T' &&
		line[6] == 'A' && line[1] == 'R' &&
		line[8] == 'T' && line[1] == ' ' &&
		line[10] == 'O' && line[11] == 'F') 
		return 1;
	return 0;
}

int end(char line[MAX_LINE_LENGTH + 1]) {
	if (line[0] == '*' && line[1] == '*' &&
		line[2] == '*' && line[3] == ' ' &&
		line[4] == 'E' && line[5] == 'N' &&
		line[6] == 'D' && line[7] == ' ' &&
		line[8] == 'O' && line[9] == 'F') 
		return 1;
	return 0;
}

void Insert_stopwords(FILE *fp1, Dict d) {
	char word[MAXWORD];
	while (fgets(line, MAX_LINE_LENGTH + 1, fp) != NULL) {
		char word1[MAXWORD];
		for (int loop = 0; word != '\n'; loop ++) {
			word1[loop] = word[loop];
		}
		word[loop] = '\0';
		DictInsert(d, word);
	}
}

int word_use_or_not(Dict d, char *word) {
	if (DictFind(word) == 0) {
		return 0;
	}
	int loop;
	for (loop = 0; word[loop] != '\0'; loop ++)
	stem(word, 0, loop - 1);
	return 1;
}