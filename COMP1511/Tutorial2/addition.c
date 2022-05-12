//Z5286124 Jinghan Wang

#include <stdio.h>

int main (void)
{
	int integerOne;
	int integerTwo;

	printf("PLease enter two integers: ");
	scanf("%d", &integerOne);
	scanf("%d", &integerTwo);

	int sum = integerOne + integerTwo;	

	printf("%d ", integerOne);
	printf("+ ");
	printf("%d ", integerTwo);
	printf("= ");
	printf("%d\n", sum);
	
	return 0;
}
