#include <iostream>

int main() {
	auto buffer = std::string{};
	std::getline(std::cin, buffer);
	std::cout << buffer << std::endl;
	return 0;
}
