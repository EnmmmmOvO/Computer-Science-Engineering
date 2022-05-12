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
		


		int result;
		scanf("%d", &result);
		array[0] = result;
		
		if (check_array(result))
		{
			if (result = 1)
			{
				
			


	}
exit:
	return 0;
}

int check_array(int result)
{
	if(result == 1 || result == 2)
	{
		return 1;
	} else if (result == -1)
	{
		goto exit;
	}
	return 0;
}


