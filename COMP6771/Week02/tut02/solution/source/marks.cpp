#include <iostream>
#include <iterator>
#include <list>
#include <vector>

int main() {
	// Manually iterating through a list (forward iteration)
	std::list<int> studentMarks1;
	studentMarks1.push_back(63);
	studentMarks1.push_back(67);
	studentMarks1.push_back(69);
	studentMarks1.push_back(74);
	studentMarks1.push_back(82);

	int medianIndex = (studentMarks1.size() / 2);
	auto it = studentMarks1.begin();
	std::advance(it, medianIndex);
	std::cout << "Median: " << *it << "\n";

	// Using a container (vector) with random access iterator
	std::vector<int> studentMarks2;
	studentMarks2.push_back(63);
	studentMarks2.push_back(67);
	studentMarks2.push_back(69);
	studentMarks2.push_back(74);
	studentMarks2.push_back(82);

	std::cout << "Median: " << studentMarks2.at(2) << "\n";
}
