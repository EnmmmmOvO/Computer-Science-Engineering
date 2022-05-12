//z5286124 Jinghan Wang



#include <stdio.h>
#include <math.h>
#define MAX_NUMBER 3


int check_array(int result);


int main (void)
{
	int keepRunning = 1;
	while (keepRunning == 1)
	{	
		int array[MAX_NUMBER] = {0};
		printf("Enter instruction: ");
		

		int time = 0;
		int result;
		while (time < MAX_NUMBER)
		{
			int number;
			scanf("%d", &number);
			array[time] = number;
			if (time == 0)
			{
				result = array[0];
			}
			if (array[0] == 1 && time == 1)
			{
				array[2] = 2;
				time ++;
			}
			time ++;
		}
		printf("%.0f\n", pow(array[1] , array[2]));
		if (check_array(result))
		{	
		} else
		{
			keepRunning = 0;
		}
	}
	return 0;
}



int check_array(int result)
{
	if(result == 0)
	{
		return 1;
	}
	return 0;
}
