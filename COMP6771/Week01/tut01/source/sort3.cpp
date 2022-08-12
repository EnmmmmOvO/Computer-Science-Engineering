#include <iostream>

void sort3(int& a, int& b, int& c) {
	if (a > b) std::swap(a,b);
	if (a > c) std::swap(a,c);
	if (b > c) std::swap(b,c);
}

void sort3(std::string& a, std::string& b, std::string& c) {
	/*if (a.compare(b) > 0) std::swap(a,b);
	if (a.compare(c) > 0) std::swap(a,c);
	if (b.compare(c) > 0) std::swap(b,c);*/
	if (a > b) std::swap(a,b);
	if (a > c) std::swap(a,c);
	if (b > c) std::swap(b,c);
}