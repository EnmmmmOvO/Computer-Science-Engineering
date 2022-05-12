//z5286124 Jinghan Wang

#include <stdio.h>
#define MAX_VALUE 4
int main (void)
{
	int array[MAX_VALUE] = {0};
	
	int times = 0;
	while (times < MAX_VALUE) 
	{
		int enterNumber;
		scanf("%d", &enterNumber);
		array[times] = enterNumber;
		times ++;
	}
	printf("\n");

	while (times > 0)
	{
		printf("%d\n", array[times]);
		times = times - 1;
	}
	return 0; 
}
