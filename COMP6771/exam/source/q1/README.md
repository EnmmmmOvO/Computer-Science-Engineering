# Question 1: Path Printer

[[_TOC_]]

## 1. Background

Computers are very good at handling data and mathematical descriptions of real-world objects. Humans on the other hand are visual creatures: unless we can see something, it is very difficult for us to manipulate it.

Take, for example, the path of a hypothetical hero walking through a 2D grid or map. Whereas computers are content knowing the bounding-box of the map and the moves made by the hero, humans would need to see the grid and have a visual distinction between points or tiles trodden by the hero and those not walked on.

Luckily, COMP6771 students are the bridge between computers and humanity.

## 2. Task

Your task is to write a small library that is able to convert between a data-oriented description of the path taken by our hero and a visual respresentation easily consumed by humans. Namely, you must implement the classes and functions whose **minimal public interface** is listed below.

### 2.1 `move`
A `move` is a single step taken in the hero's journey. Each move displaces the hero according to its direction. The moves and their displacements are listed below.

```cpp
enum class move : uint8_t {
    NN,
    SS,
    WW,
    EE,
    NW,
    NE,
    SW,
    SE,
};
```

|Move|Displacement|
|-|-|
|`move::NN`|(0, -1)|
|`move::SS`|(0, 1)|
|`move::WW`|(-1, 0)|
|`move::EE`|(1, 0)|
|`move::NW`|(-1, -1)|
|`move::NE`|(1, -1)|
|`move::SW`|(-1, 1)|
|`move::SE`|(1, 1)|

Note that in this world moving down increases one's vertical displacement rather than moving up as in the Cartesian Plane. Moving right increases the horizontal displacement as per usual.

### 2.2 `style`

`style` is a polymorphic base class that applies some visual style to every tile of the map. It should be extendable so that future developers can reuse our code with minimal overhead.

#### 2.2.1 Constructors
```cpp
style();                           // 1
```
```cpp
explicit style(char background);   // 2
```
1) Default constructor.
- Should construct this style with a default background character of a single space.

2) Direct constructor.
- Should construct this style with the given background character.

#### 2.2.2 Destructor
```cpp
~style() noexcept;
```
Destructs the given style, freeing any resources held.

Note: the given prototype may not be complete.

#### 2.2.3 Member Functions
```cpp
virtual style_tile() const -> char;                                 // 1
```
```cpp
virtual style_tile(move end_move) const -> char;                    // 2
```
```cpp
virtual style_tile(move prev_move, move curr_move) const -> char;   // 3
```
Styles a tile in the map from the hero's quest.

1) Styles a background tile with the background given in the relevant constructor.
- Should be overridable by any derived classes.
2) Styles the end tile.
- For `style`, this should be `'0'`
3) Styles a path tile.
- The style may change depending on what kind of move is made.
- For `style`, all tiles walked should be styled with a `'*'`, regardless of what direction the move was in.

#### 2.2.4 Other class requirements

* `style` must be copy- and move-constructible, as well as copy- and move-assignable.

### 2.3 `detailed_style`

A `detailed_style` is everything that a `style` is, but more detailed. It must extend and override some of the default style's behaviour.

#### 2.3.1 Constructors
```cpp
detailed_style(char end_1, char end_2);
```
Constructs the given `detailed_style` with two possible end tiles, as well as with a background tile of `+`.

#### 2.3.2 Member Functions
```cpp
style_tile(move end_move) const -> char;                 // 1
style_tile(move prev_move, move curr_move) const -> char;   // 2
```

Styles a tile from the map in the hero's journey.
1) Styles the end tile
- If the number of moves made is **greater** than 8, should use the `end_1` ending style given in the constructor
- Otherwise, use the `end_2` style
- **Note**: the given function prototype may be incomplete.
2) Styles a tile walked on by the hero.
- When `prev_move != curr_move`:
    - `move::NN` and `move::SS` should be styled as `|`
    - `move::EE` and `move::WW` should be styled as `-`
    - `move::NE` and `move::SW` should be styled as `/`
    - `move::NW` and `move::SE` should be styled as `\`
- When `prev_move == curr_move`:
    - `move::NN` should be styled as `^`
    - `move::SS` should be styled as `v`
    - `move::EE` should be styled as `>`
    - `move::WW` should be styled as `<`
    - `move::NE`, `move::SW`, `move::NW`, and `move::SE` should be styled as in the previous point
- **Note**: the given function prototype may be incomplete.

#### 2.3.3 Other class requirements

* `detailed_style` must be copy- and move-constructible, as well as copy- and move-assignable.

### 2.4 `make_map`
```cpp
using map = std::vector<std::vector<char>>;

// Get the tile at co-ordinate (x, y)
// Provided for you
auto at(const map &mp, int x, int y) -> char;
auto at(map &mp, int x, int y) -> char&;

auto make_map(const std::vector<move> &path, const style &styler) -> map;
```
Given a vector of moves made by the hero and a polymorphic styler, returns a new `map` that is the styled landscape the hero traversed.

The hero always starts in the top-left corner of the map at displacement (0, 0) and finishes in the bottom-right corner (m, n). _m_ and _n_ is equal to the sum total displacements given by the moves made.

For example,
```cpp
auto styler = style{};
auto moves = std::vector<move>{
    move::EE, // go to (1, 0)
    move::SS, // go to (1, 1)
    move::SS, // go to (1, 2)
    move::EE, // go to (2, 2)
    move::NN, // go to (2, 1)
    move::SE, // go to (3, 2)
}

auto mapped = make_map(path, styler);

CHECK(at(mapped, 3, 2) == '0'); // end tile
CHECK(at(mapped, 3, 0) == ' '); // not walked by the hero
```
sees the hero end his journey at (3, 2), so `m == 3` and `n == 2`. Thus, the map should have (3 + 1) x (2 + 1) == 12 tiles total. Remember: tiles are zero-based!

**Important**: You should style the start tile the same as the end tile

### 2.5 Implementation hints

* It may be beneficial to first figure out which points on the map each move takes the hero to.
* Styling can be done during the above process, or as a separate pass afterwards.
* Remember, a move always takes the hero from where he is to an adjacent tile. When styling, you are effectively adding a style for where the hero _was_ and **not** where they end up. The only exception to this rule is styling the end tile.
    * There is an example of this in the provided test file.
* You should always access the `map` with the provided `at()` functions. `std::vector` stores its memory in so-called "row major" order, which would make accessing tiles unnecessarily tricky.

## 3 Assumptions & Constraints
* All moves will leave the hero at a point (i, j) where `i >= 0` and `j >= 0`.
* There is at least one tile in the map.
* It is possible to walk in a loop or to otherwise walk over tiles previously walked on.
* We will use a styler different to `style` and `detailed_style` during testing.
* There is a 60 second time limit on all autotests.

## 4. Mark Breakdown

The approximate proportion of marks for this question are given below:
* 20% given to the correct implementation of `style`.
* 30% given to the correct implementation of `detailed_style`.
* 50% given to the correct implementation of `make_map`.