//z5286124 Jinghan Wang

#include <stdio.h>

#include <stdio.h>

#define MAX_DIGITS 10

int main(void) 
{
	int pi[MAX_DIGITS] = {3, 1, 4, 1, 5, 9, 2, 6, 5, 3};
	printf("How many digits of pi would you like to print? ");
	int digits;
	scanf("%d", &digits);
	
	int number = 0;

	while (number < digits) 
	{
		if (number == 1)
		{	
			printf(".");
		}
		printf("%d", pi[number]);
		number ++;
	}


	printf("\n");



    return 0;
}
