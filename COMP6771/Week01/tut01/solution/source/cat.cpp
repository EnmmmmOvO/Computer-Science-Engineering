#include <iostream>
#include <string>

auto main() -> int {
  // a std::string is a dynamically-sized character array, which
  //  means we are not required to worry about the fixed-sized arrays
  //  that we're used to in C. In this way it makes it harder to overflow
  //  a char array or waste memory. std::string is also a class meaning
  //  a lot of important pieces of data associated with the types are stored in
  //  the object itself (e.g. size). Strings also have the added benefits
  //  of providing an iterator to loop through the string
  auto buffer = std::string{};


  // reads all characters from the character input in, until '\n' is read, and
  // writes them into our string object, `buffer` ('\n' is not written). `buffer`
  // will automatically grow in size, just like a vector.
  std::getline(std::cin, buffer);

  // printf has some benefits such as complex format strings, but is error-prone,
  // and lacks type-safety. Using streams like `std::cout` gives us compile-time
  // safety, by deferring the "print" operation to the type of the object we're
  // printing.
  std::cout << buffer << "\n";
  return 0;
}
