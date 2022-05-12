
//z5286124 Jinghan Wang

#include <stdio.h>

int main (void)
{
	int numberEnter;

	printf("Enter number: ");
	scanf("%d", &numberEnter);
		
	printf("The factors of %d are:\n", numberEnter);
	
	int number = 1;
	int sum = 0;
	while (number <= numberEnter)
	{
		int remainder = numberEnter % number;
		if (remainder == 0)
		{
			printf("%d\n", number);	
			sum = sum + number;
		}
		number ++;
	}
	
	printf("Sum of factors = %d\n", sum);

	int remainderSum1 = sum % numberEnter;
	int remainderSum2 = numberEnter % sum;

	if (remainderSum1 == 0 || remainderSum2 == 0)
	{
		printf("%d is a perfect number\n", numberEnter);	
	} else
	{
		printf("%d is not a perfect number\n", numberEnter);
	}

	return 0; 
}

