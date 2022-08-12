# Question 2: Scope Guard

[[_TOC_]]

## 1. Background

As we have learnt, resource safety and finalistic destruction is one of the reasons why C++ is so widely used. As a reminder, the primary idiom around resource safety is RAII:
- **R**esource
- **A**cquisition
- **I**s
- **I**nitialisation

RAII is implemented by acquiring resources in a class-type's constructor and releasing that resource in its destructor.

This mechanism works extremely well, but having to write a custom class type for _every_ resource can be a prohibitive hassle.

We can do better.

## 2. Task

Your task is to write a class template called `scope_guard` that provides the user with the ability to have RAII semantics for any nullable resource of type `T` with minimal code.

`T` must be a nullable type, meaning that a default-constructed `T` must represent its "invalid" value.
An example of a nullable `T` is `unique_ptr<int>`, where `auto ptr = unique_ptr<int>{};` assigns to `ptr` an invalid `unique_ptr<int>`. **Henceforth, the default-constructed `T` will be known as the "null value".**

A `scope_guard` can either be in the "present" state or the "absent state". The present state is when an instance of `scope_guard<T>` contains a live resource that will eventually be freed. The absent state is when `scope_guard`'s underlying resource is the null value.

The **public** interface of `scope_guard` is given below.

### 2.1 Template Parameters

```cpp
template <typename T, auto C, auto D>
class scope_guard;
```
`T` - the (possibly const/volatile qualified) type of the underlying resource.

`C` - a non-type template parameter of a functor that accepts some number and type of arguments and constructs a T.

`D` - a non-type template parameter of a functor which accepts a `T&` and destructs it

Both `C` and `D` have a `noexcept` guarantee.

### 2.2 Member Types

`scope_guard` must have these public member typedefs.

|Member Type|Definition|
|-|-|
|`ctor_type`| The type of the constructor function|
|`dtor_type`| The type of the dtor function|
|`resource_type`| `T`, with all `const` and `volatile` modifiers removed. |
|`handle`| `resource_type` if `is_sso_v` is true (see sec. 2.6), `const resource_type&` otherwise|

### 2.3 Constructors
```cpp
scope_guard() noexcept;                         // 1
```
```cpp
template <typename ...Args>
scope_guard(Args &&...args);                    // 2
```
```cpp
scope_guard(const scope_guard &other) = delete; // 3
```
```cpp
scope_guard(scope_guard &&other) noexcept;      // 4
```

1) Default constructor:
- Constructs the `scope_guard` into the absent state.
2) Direct constructor:
- Accepts 1 or more arguments and **forwards** these arguments to `C`, initialising the underlying resource with its return value.
- If the number of arguments passed to this constructor DO NOT match the number of arguments `ctor_type` expects, an exception of type `std::logic_error` should be thrown.
3) Copy constructor:
- Must be deleted
4) Move constructor:
- Moves the underlying resource of `other` into `*this`.
- Afterwards, `other` must be in the absent state .

### 2.4 Destructor
```cpp
~scope_guard() noexcept;
```
Destructs a `scope_guard` by invoking `D` with its underlying resource, if present.

### 2.5 Member Functions
```cpp
auto operator=(const scope_guard &other) -> scope_guard& = delete;  // 1
auto operator=(scope_guard &&other) noexcept -> scope_guard&;       // 2
```
1) Copy-assign:
- must be deleted
2) Move-assign:
- Destructs the underlying resource if present and moves the contents of `other` into `*this`.
- Afterwards, `other` must be in the absent state

```cpp
operator bool() const noexcept;
```
Implicit conversion operator to `bool`.

Returns:
- `true` if the `scope_guard` is in the present state.
- `false` otherwise

```cpp
auto operator*() const -> /* Unspecified */;   // 1
auto operator->() const -> /* Unspecified */;  // 2
```
1) Dereference operator.
- When `T` is a pointer type, returns a reference to the managed object. For example, if `resource_type` is `int *`, this function would return an `int&`.
- Otherwise, throws an exception of type `std::logic_error`

2) Member access operator:
- When `T` is a pointer type, returns the pointer to the managed object. For example, if `resource_type` is `int *`, this function would return an `int*`.
- Otherwise, throws an exception of type `std::logic_error`

Note: you will need to choose the best return type for these functions.

```cpp
auto operator==(const scope_guard &other) const noexcept -> bool;
```
C++20-style equality operator.

Returns:
- `true` if `*this` and `other` are both in the present state and the underlying resources are equal OR they are both in the absent state.
- `false` otherwise

```cpp
auto get() const noexcept -> handle;
```
Returns a handle to the underlying resource.

### 2.6 Type Traits

```cpp
template <typename T>
struct is_sso;                              // 1

template <typename T>
constexpr auto is_sso_v = /* unspecified */; // 2
```
1) `is_sso` (SSO == small-space optimised):
- A type trait that, for a given T, provides a boolean data member `value` which:
- is `true` if and only if `sizeof(T) <= sizeof(T*)` and `T` is trivial with rank 0 (see below).
- as a special case, is `true` if `T` is a `char[6]`, `char[7]`, or `char[1]`.
- is `false` otherwise.
2) `is_sso_v`:
- A variable template which is `true` when `is_sso<T>::value` is true and false otherwise.

The rank of a type is how many`[]` appear in its declaration. For example:
- `int` -> rank 0
- `int[]` -> rank 1
- `int[][]` -> rank 2

Both `is_sso` and `is_sso` are non-member helpers of `scope_guard`. They should be defined outside of the class.

### 2.7 Implementation Hints

* Make sure you follow the prototypes given in the spec **exactly** otherwise your code will not compile.
* There are lots of nifty things in the standard library that will make your implementation terse.
* The Direct Constructor's exception requirement will likely take a long time to figure out. Leave it until last.

### 2.8 Usage Example

With a `scope_guard`, it should be possible to write code like below
```cpp
struct fd_t {
    int fd = -1; // secret way to generate a default ctor
};

int times_called = 0;

auto open(const char *file, int mode) -> fd_t {
    ++times_called;
    /* OS stuff */
}

auto write(int os_fd, std::size_t n_bytes, const char *buf) -> std::ssize_t {
    /* more OS stuff */
}

auto close(fd_t &f) -> void {
    ++times_called;
    /* even more OS stuff */
}

int main() {
    using unique_file = scope_guard<fd, open, close>;

    {
        auto fd = unique_file{"swag.txt", O_RW};
        auto msg = std::string_view{"foo"};
        write(fd.get(), msg.size(), msg.data());
        auto fd2 = fd; // won't compile
        auto fd2 = std::move(fd); // OK, transfer ownership
    }   // no resource leak!

    std::cout << times_called << std::endl; // prints 2
}
```

## 3. Assumptions & Constraints

* `T` will always be nullable and support all the necessary operators that `scope_guard` requires to function.
* `scope_guard` will never be instantiated with an array type. `is_sso` may be, however.
* `C` and `D` are always callable and will not crash the program.
* You can modify the `private` interface of `scope_guard` as much as you like to ensure that all of the listed functionality in the above spec is fulfilled.
* If you wish, you may add to the public interface.
* All exception messages are optional. You need only ensure that your code throws exceptions of the correct type.
* There is no performance requirement for this task.
* There are no style or testing marks associated with this question

## 4. Mark Breakdown

For this question, the approximate mark allocations are:
* 15% for required member types
* 25% for required constructors
* 15% for required destructors
* 25% for required members
* 20% for required type traits
