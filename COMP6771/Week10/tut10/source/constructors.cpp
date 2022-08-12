#include <list>
#include <iostream>

class purple {
public:
	purple() {
		std::cout << "ctor ";
	}
	purple(purple const&) {
		std::cout << "copy-ctor ";
	}
	~purple() {
		std::cout << "dtor ";
	}
};

int main() {
	{
		std::cout << "Pointer: "
		std::list<purple*> l;
		purple x;
		l.push_back(&x);
	}
	{
		std::cout << "\nValue: "
		std::list<purple> l;
		purple x;
		l.push_back(x);
	}
}
