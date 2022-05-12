#include <stdio.h>

int main (void)
{
	int endLoop = 0;
	
	while (endLoop == 0)
	{
		int inputNumber;
		scanf("%d", &inputNumber);
		if (inputNumber % 2 == 0)
		{
			printf("the number is even.\n");
		} else
		{
			printf("the number is odd.\n");
		}
		endLoop = 1;
	}

	




}



