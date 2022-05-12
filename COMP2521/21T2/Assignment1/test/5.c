#include <stdio.h>
#include <assert.h>
#include <ctype.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXLINE 1000
#define MAXWORD 100

#define isWordChar(c) (isalnum(c) || (c) == '\'' || (c) == '-')

// add function prototypes for your own functions here

int word_use_or_not(char *word);

int main(int argc, char *argv[]) {
	FILE *fp;


	fp = fopen(argv[1], "r");
    

    char line[MAXLINE];

	while (fgets(line, MAXLINE + 1, fp) != NULL) {
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
                    printf("%s\n", word);
                } 
                start = loop + 1;
			}
		}	
	}
}

int word_use_or_not(char *word) {
    if (word[0] == ' ') {
        return 0;
    }
    char a[MAXLINE];
    FILE *fp1;
    fp1 = fopen("stopwords", "r");
    while(fgets(a, MAXLINE + 1, fp1) != NULL) {
        char *find = strchr(a,'\n');
        *find = '\0';
        if (a == word) {
            return 0;
        }
    }
    return 1;
}