#include <iterator>
#include <set>
#include <stdexcept>
#include <type_traits>

template <typename T>
class streaming_median {
 public:
  auto add(T value) -> void { data_.insert(std::move(value)); }

  auto median() const -> T {
    if (data_.empty()) {
      throw std::runtime_error{"Cannot get median of empty stream."};
    }

    if (data_.size() % 2 == 0) {
      throw std::runtime_error{"Cannot get median of an evenly sized stream."};
    }

    return *std::next(data_.begin(), data_.size() / 2);
  }

 private:
  std::multiset<T> data_;
};