//z5286124 Jinghan Wang
//
// This program was written by Jinghan Wang (z5286124)
// on 11-10-2020
//
// This program prints out facts about a circle given its radius,
// using functions.
//

#include <stdio.h>
#include <math.h>



double area(double radius);
double circumference(double radius);
double diameter(double radius);


int main(void) {
    double radius;

    printf("Enter circle radius: ");
    scanf("%lf", &radius);

    printf("Area          = %lf\n", area(radius));
    printf("Circumference = %lf\n", circumference(radius));
    printf("Diameter      = %lf\n", diameter(radius));

    return 0;
}


// Calculate the area of a circle, given its radius.
double area(double radius) {
	double area;
	area = M_PI * radius * radius;
    return area; 
}

// Calculate the circumference of a circle, given its radius.
double circumference(double radius) {
    double circumference;
	circumference = M_PI * radius * 2;
	return circumference; 
}

// Calculate the diameter of a circle, given its radius.
double diameter(double radius) {
    double diameter;
	diameter = radius * 2;
    return diameter; 
}
