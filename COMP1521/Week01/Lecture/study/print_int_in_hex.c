#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

int main (int argc, char *argv[]) {
    uint32_t value = 0;
    printf("Enter a positive int : ");
    scanf("%u", &value);
    printf("%u = 0x%08x\n", value, value & 0xFFFFFFFF);    
    return 0;
}