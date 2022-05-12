//Jinghan Wang
//z5286124

#include <stdio.h>
#include <string.h>

#define MAX_VALUE 1024

int main(void) {
	char character[MAX_VALUE];
	int loop = 0;
	while (fgets(character, MAX_VALUE, stdin) != NULL) {
		if (strlen(character) % 2 == 0) {
			fputs(character, stdout);
		}
		loop ++;
	}

	return 0;
}
