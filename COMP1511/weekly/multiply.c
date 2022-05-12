//z5286124 Jinghan Wang


#include <stdio.h>


int main (void)
{
	int integerA;
	int integerB;

	scanf("%d", &integerA);
	scanf("%d", &integerB);
	
	int multiply = integerA * integerB;

	if (multiply == 0)
	{
		printf("zero\n");
	} else
	{
		if (integerA > 0 && integerB > 0)
		{
			printf("%d\n", multiply);
		} else if (integerA < 0 && integerB < 0)
		{
			printf("%d\n", multiply);
		} else 
		{		
			printf("%d\n", -multiply);
		}
	}

	return 0;
}
