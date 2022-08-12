#include <iostream>
#include <list>
#include <numeric>

int main() {
	std::list<int> studentMarks;
	studentMarks.push_back(63);
	studentMarks.push_back(67);
	studentMarks.push_back(69);
	studentMarks.push_back(74);
	studentMarks.push_back(82);

	auto it = studentMarks.cbegin();
	std::advance(it, studentMarks.size() / 2);
	std::cout << "Median: " << *it << "\n";
}