//z5286124 Jinghan Wang

#include <stdio.h>

#define MAX_VALUE 36


int main (void)
{
	int array[MAX_VALUE] = {0};
	
	int time = 1;
	while (time <= MAX_VALUE)
	{
		int enterNumber = -1;
		scanf("%d", &enterNumber);
		if (enterNumber == -1)
		{
			break;
		}
		array[enterNumber] = 1;
		time ++;
	}

	int i = 0;
	while (i < MAX_VALUE)
	{
		printf("%d", array[i]);
		i ++;
	}
	printf("\n");
	return 0;
}
