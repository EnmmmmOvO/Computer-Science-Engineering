#include "./stack.hpp"

template <typename T>
void stack<T>::push(T t) {
  stack_.push_back(t);
}

template <typename T>
T stack<T>::pop() {
  return stack_.pop_back();
}
