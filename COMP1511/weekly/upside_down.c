//z5286124 Jinghan Wang

#include <stdio.h>


int main (void)
{
	double integerA;
	double integerB;
	double integerC;
	
	printf("Please enter three numbers: ");
	scanf("%lf", &integerA);
	scanf("%lf", &integerB);
	scanf("%lf", &integerC);

	if (integerA > integerB && integerB > integerC)
	{
		printf("down\n");
	}
	else if (integerA < integerB && integerB < integerC)
	{
		printf("up\n");
	} else 
	{
		printf("neither\n");
	}

	return 0;

}
