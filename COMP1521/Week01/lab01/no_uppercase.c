//Jinghan Wang
//z5286124

#include <stdio.h>
#include <ctype.h>

int main(void) {
	int character;
	while ((character = getchar()) != EOF) {
		if (isupper(character)) {
			character = tolower(character);
		}
		putchar(character);
	}
	return 0;
}
