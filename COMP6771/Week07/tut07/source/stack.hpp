#ifndef LECTURES_WEEK7_STACK_H_
#define LECTURES_WEEK7_STACK_H_

#include <vector>

template <typename T>
class stack {
 public:
  auto push(T) -> void;
  auto pop() -> T;
 private:
  std::vector<T> stack_;
};

#endif  // LECTURES_WEEK7_STACK_H_
