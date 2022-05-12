#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#define MAX_NUM_WORDS	(10000)
#define	MAX_WORD_LEN	(100)

int main(int argc, char * argv[]) {
	assert(argc >= 3);
	int width = atoi(argv[1]);
	char mode = argv[2][0];

	char words[MAX_NUM_WORDS][MAX_WORD_LEN];
	int numWords = 0;

	while (scanf("%s", words[numWords]) != EOF) {
		numWords++;
	}

	int begin = 0;
	int end = begin;

	int lineLength = 0;
	int leadingSpace = 0;

	while (end < numWords) {
		int first = 1;
		lineLength = 0;
		int outOfBound = 0;
		while (end < numWords && outOfBound != 1) {
			if (first == 1) {
				lineLength += strlen(words[end]);
				first = 0;
				end++;
			} else {
				if (lineLength + 1 + strlen(words[end]) <= width) {
					lineLength += 1;
					lineLength += strlen(words[end]);
					end++;
				} else {
					outOfBound = 1;
				}
			}
		}

		if (mode == 'L') {
			printf("%s", words[begin]);
			int i;
			for (i = begin + 1; i < end; i++) {
				printf(" %s", words[i]);
			}
			printf("\n");
		} else {
			leadingSpace = width - lineLength;
			int i;
			for (i = 0; i < leadingSpace; i++) {
				printf(" ");
			}
			printf("%s", words[begin]);
			for (i = begin + 1; i < end; i++) {
				printf(" %s", words[i]);
			}
			printf("\n");
		}

		begin = end;
	}

	return 0;
}
