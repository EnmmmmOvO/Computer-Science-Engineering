//Z5286124 Jinghan Wang

#include <stdio.h>


int main (void) 
{
	int enterNumber;
	scanf("%d", &enterNumber);

	if (enterNumber < 0) {
		printf("Don't be so negative!\n");
	} else if (enterNumber == 0) {
		printf("You have entered zero.\n");
	} else {
		printf("You have entered a positive number.\n");
	}

	return 0;
}
