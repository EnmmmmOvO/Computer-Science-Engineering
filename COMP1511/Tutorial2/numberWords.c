//Z5286124 Jinghan Wang

#include <stdio.h>

#define MIN_VALUE 1
#define MAX_VALUE 5

int main (void) 
{
	int enterNumber;

	printf("Please enter an integer: ");
	scanf("%d", &enterNumber);
	
	if (enterNumber > MAX_VALUE) {
		printf("You entered a number greater than five.\n");
	} else if (enterNumber < MIN_VALUE) {
		printf("You entered a number less than one.\n");
	} else if (enterNumber == 1) {
		printf("You entered one.\n");
	} else if (enterNumber == 2) {
		printf("You entered two.\n");
	} else if (enterNumber == 3) {
		printf("You entered three.\n");
	} else if (enterNumber == 4) {
		printf("You entered four.\n");
	} else if (enterNumber == 5) {
		printf("You entered five.\n");
	}
	
	return 0;
	
}
