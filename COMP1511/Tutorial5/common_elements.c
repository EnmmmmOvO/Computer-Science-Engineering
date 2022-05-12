//z5286124 Jinghan Wang

#include <stdio.h>

int common_elements(int length, int source1[length], int source2[length], int 
destination[length]); 

int main (void)
{
	int array1[7] = {1,5,5,3,6,7,8};
	int array2[7] = {3,4,1,3,6,7,9};
	int array3[7] = {0};
	int length = 7;
	int number = common_elements(length, array1, array2, array3);
	int numberD = 0;
	while (numberD < number)
	{
		printf("%d\n", array3[length]);
		numberD ++;
	}
	return 0;
}


int common_elements(int length, int source1[length], int source2[length], int 
destination[length]) 
{
	int numberA = 0;
	int numberB = 0;
	while (numberB < length)
	{
		int numberC = 0;
		while (numberC < length)
		{
			if (source1[numberB] == source2[numberC])
			{
				destination[numberA] = source1[numberB];
				numberA ++;
				break;
			}
			numberC ++;
		}
		numberB ++;
	}
    return numberA;
}
// You may optionally add a main function to test your common_elements function.
// It will not be marked.
// Only your common_elements function will be marked.
