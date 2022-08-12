#include <iostream>

#include "./stack.hpp"

auto main() -> int {
  stack<int> is1;
  is1.push(5);
  std::cout << is1.pop() << "\n";
}