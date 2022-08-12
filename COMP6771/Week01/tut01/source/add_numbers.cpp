#include <iostream>

int getInteger() {
    int temp = 0;
    if (std::cin >> temp) {
        return temp;
    } else {
        std::cerr << "Something went wrong while reading an integer, bailing..." << std::endl;
		exit(1);
    }
}

int main() {
    std::cout << "Please enter two numbers: ";
    int sum = 0;
    for (int loop = 0; loop < 2; loop++) sum += getInteger();
    std::cout << "Sum: " << sum << std::endl;
    return 0;
}
