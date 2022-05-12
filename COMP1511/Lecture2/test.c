#include <stdio.h>

int main (void)
{
	int diceInputOne;
	int diceInputTwo;
	int target;

	printf("Please enter the first size of the dice: ");
	scanf("%d", &diceInputOne);
	printf("Please enter the second size of the dice: ");
	scanf("%d", &diceInputTwo);
	printf("Please enter the target: ");
	scanf("%d", &target);

	int diceOneValue = 1;

	int times = 0;
	int targets = 0; 

	while (diceOneValue <= diceInputOne) 
	{
		int diceTwoValue = 1;

		while (diceTwoValue <= diceInputTwo) 
		{
			times++;
			int total = diceOneValue + diceTwoValue;
			if (total == target) 
			{
				targets++;
				printf("diceOne is %d  diceTwo is %d  Total is %d\n", diceOneValue, diceTwoValue, total);
			}	
			diceTwoValue++;
		}
	diceOneValue++;
	}


	printf("totaltime: %d, %d times match.\n", times, targets);

	double value = (targets * 1.0 / times) *100;
	printf("%lf percent \n", value);
	return 0;
}
