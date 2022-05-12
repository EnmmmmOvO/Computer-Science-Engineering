//Jinghan Wang
//z5286124

#include <stdio.h>
#include <string.h>

int main(void) {
	char character;
	while (scanf("%c", &character) != EOF) {
		switch (character) {
			case 65:
			case 69:
			case 79:
			case 73:
			case 85:
			case 97:
			case 101:
			case 105:
			case 111:
			case 117: break;
			default: printf("%c", character); break;
		}
	}
	return 0;
}
