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

// add function prototypes for your own functions here

int main(int argc, char *argv[]) {
	FILE *fp;
	fp = fopen("stopwords", "r");

    char word[MAXLINE];
    char *a = "able";
    while(fgets(word, MAXLINE + 1, fp) != NULL) {
        char *find = strchr(word, "\n\000");
        *find = '\0';
        for(int loop = 0; word[loop] != '\0' || a[loop] != '\0'; loop ++) {
            if (word[loop] == a[loop]) {
                printf("1\n");
            }
        }
    }

	return 0;
}
