//z5286124 Jinghan Wang


#include <stdio.h>

int main (void)
{
	int numberA;
	printf("How many numbers: ");
	scanf("%d", &numberA);

	int loop = 1;
	int total = 0;
	while (loop <= numberA)
	{
		int numberB = 0;
		scanf("%d", &numberB);
		total = total + numberB;
		loop ++;
	}
	printf("The sum is: %d\n", total);
	return 0;


}

