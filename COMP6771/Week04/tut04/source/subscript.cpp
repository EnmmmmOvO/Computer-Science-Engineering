#include <cassert>
#include <iostream>

class point {
public:
	point(int x, int y) : x_(x), y_(y) {}
	int& operator[](int i) {
		assert(i == 0 || i == 1);
    	return i == 0 ? this->x_ : this->y_;
	}
private:
	int x_;
	int y_;
};

int main() {
	auto q = point{99, -5};
	/*q[0] = -99;
	std::cout << q[0] << "\n";
	auto const p = point{99, -5};
	std::cout << p[0] << "\n";*/
}
