//Jinghan Wang
//z5286124

#include <stdio.h>

int main(int argc, char **argv) {
	printf("Program name: %s\n", argv[0]);
	if (argc == 1) {
		printf("There are no other arguments\n");
	} else {
		printf("There are %d arguments:\n", argc - 1);
	}
	for (int loop = 1; loop < argc; loop ++) 
	    printf ("	Argument %d is \"%s\"\n", loop, argv[loop]);
	return 0;
}
