//z5286124 Jinghan Wang

#include <stdio.h>

int main (void)
{
	int numberEnter;
	
	printf("Enter number: ");
	scanf("%d", &numberEnter);
	
	int number = 1;

	while (number < numberEnter) 
	{
		int remainderA = number % 3;
		int remainderB = number % 5;	

		if (remainderA == 0 || remainderB == 0)
		{
			printf("%d\n", number);
		}
		number ++;
	}

	return 0;
}
