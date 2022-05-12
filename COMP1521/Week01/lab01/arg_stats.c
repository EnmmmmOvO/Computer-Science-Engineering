//Jinghan Wang 
//z5286124

#include <stdio.h>
#include <stdlib.h>

int min(int len, int array[100]);
int max(int len, int array[100]);
int sum(int len, int array[100]);
int prod(int len, int array[100]);
int mean(int len, int array[100]);

int main(int argc, char **argv) {
	int len = argc - 1;
	int array[100] = {0};
	for (int loop = 0; loop < len; loop ++)
		array[loop] = strtol(argv[loop + 1], NULL, 10);

	printf("MIN:  %d\n", min(len, array));
	printf("MAX:  %d\n", max(len, array));
	printf("SUM:  %d\n", sum(len, array));
	printf("PROD: %d\n", prod(len, array));
	printf("MEAN: %d\n", mean(len, array));
	return 0;
}

//find and return the minimum
int min(int len, int array[100]) {
	int min = array[0];
	for (int loop = 0; loop < len; loop ++) 
		min =  min < array[loop] ? min : array[loop];
	return min;
}

//find and return the maximum
int max(int len, int array[100]) {
	int max = array[0];
	for (int loop = 0; loop < len; loop ++) 
		max =  max > array[loop] ? max : array[loop];
	return max;
}

//count and return the summary
int sum(int len, int array[100]) {
	int sum = 0;
	for (int loop = 0; loop < len; loop ++) 
		sum += array[loop];
	return sum;
}

//count and return the product
int prod(int len, int array[100]) {
	int prod = 1;
	for (int loop = 0; loop < len; loop ++) 
		prod =  prod * array[loop];
	return prod;
}

//find and return the average
int mean(int len, int array[100]) {
	return sum(len, array) / len;
}
