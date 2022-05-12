#include <stdio.h>

int main (void)
{
    int integerA;
    int integerB;
    int integerC;

    printf("Enter integer: ");
    scanf("%d", &integerA);
    printf("Enter integer: ");
    scanf("%d", &integerB);
    printf("Enter integer: ");
    scanf("%d", &integerC);

    int middle;

    if (integerA >= integerB)
    {
        if (integerC >= integerA)
        {
            middle = integerA;
        }
        if (integerC <= integerB)
        {
            middle = integerB;
        }
        if (integerC < integerA && integerC > integerB)
        {
            middle = integerC;
        }
    } else {
        if (integerC <= integerA)
        {
            middle = integerA;
        }
        if (integerC >= integerB)
        {
            middle = integerB;
        }
        if (integerC > integerA && integerC < integerB)
        {
            middle = integerC;
        }
    }

    printf("Middle: %d\n", middle);
    return 0;
}