# Tutorial 4

## Question 1

Why would this be considered not a very wise decision to provide this overload?

```cpp
class Point {
  public:
    Point& operator+=(const Point& p);
    Point& operator-=(const Point& p);
    Point& operator*=(const Point& p);

  private:
    int x_;
    int y_;
};

Point& Point::operator*=(const Point& p) {
  this->x_ *= p.x_;
  this->y_ *= p.y_;
  return *this;
}
```

## Question 2

Why are some operator overloads done as member functions, and others as friends?

## Question 3

Look at `source/istream.cpp`.

Complete the istream operator overload to read in two points from command line.

## Question 4

Are the following lines constructions or assignments?

```cpp
std::vector<int> a(1, 2)
```

```cpp
std::vector<int> a{1, 2}
```

```cpp
std::vector<int> b = {1, 2}
```

```cpp
std::vector<int> c = a
```

```cpp
c = b
```

## Question 5

Look at `source/type.cpp`

Modify this code to have a non-explicit type overload for a double that returns the length from the origin to the point's current coordinates.

## Question 6

Look at `source/book.h` and `source/book.cpp`

* Write the function definition for a constructor that takes values for name, author, isbn and price and uses a member initializer list to set the value of each data member.
* Write the overloaded == operator to compare if two book objects are identical
* Write the overloaded != operator that calls the already overloaded == operator to return true when two book objects are not identical.
* Write the overloaded << operator to print out the name, author, isbn and price of a book using std::cout
* Write the overloaded type conversion operator to enable the conversion of the Book class to a std::string in the form of "author, name"
* Create a main function that creates a `std::vector<book>`, add a few Book objects into the vector with different isbn numbers and prices
* Write the overloaded < operator to allow you to sort books by their isbn number. Test this in your main method using std::sort
* Call std::sort again with a lambda function as the predicate that sorts the books by price.

## Question 7

Look at `source/subscript.cpp`

* Make this code const-correct so it can compile and run sucessfully
* In what cases would we need to overload an operator for its const or non-const version?

## Question 8

What are examples of commonly used C++ exception types? When would we use them?
