//z5286124 Jinghan Wang

#include <stdio.h>

int main (void)
{
	int integerA;
	int integerB;
	int integerC;

	printf("Enter integer: ");
	scanf("%d", &integerA);
	printf("Enter integer: ");
	scanf("%d", &integerB);
	printf("Enter integer: ");
	scanf("%d", &integerC);

	int numberA = (integerA >= integerB) ? integerA:integerB;
	int numberB = (integerA < integerB) ? integerA:integerB;
	int max = (numberA >= integerC) ? numberA:integerC;
	int min = (numberB < integerC) ? numberB:integerC;
	int mid = integerA + integerB + integerC - max - min;

	printf("Middle: %d\n", mid);
	return 0;
}
