//Z5286124 Jinghan Wang
#include <stdio.h>

int main (void) 
{
	int diceSide;
	int rollTimes;

	printf("Enter the number of sides on your dice: ");
	scanf("%d", &diceSide);
	printf("Enter the number of dice being rolled: ");
	scanf("%d", &rollTimes);

	int rangeMax = rollTimes * diceSide;

	double total = rollTimes + rangeMax;

	if (diceSide <= 0 || rollTimes <= 0)
	{
		printf("These dice will not produce a range.\n");
	} else
	{
		printf("Your dice range is ");
		printf("%d", rollTimes);
		printf(" to ");
		printf("%d.\n", rangeMax);
		printf("The average value is %f\n", total / 2);
	}

	return 0;
}
