//z5286124 Jinghan Wang



#include <math.h>
#include <stdio.h>
#define MAX_VALUE 3





int main (void)
{
	int keepRunning = 1;
	while (keepRunning == 1)
	{
		int array[MAX_VALUE] = {0};
		printf("Enter instrution: ");
	
		int time = 0;
		//int result;
		while (time < MAX_VALUE)
		{
			int number;
			scanf("%d", &number);
			array[time] = number;
			if (array[0] == 1 || time == 1)
			{
				array[2] = 2;
				time ++; 
			}
			time ++;
		}
		if (array[0] == 1 || array[0] == 2)
		{
			printf("%.0f\n", pow(array[1] , array[2]));
		} else
		{
			keepRunning = 0;
		}

	}
	return 0;
}
