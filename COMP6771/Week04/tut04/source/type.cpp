#include <vector>

class point {
  public:
    point(int x, int y) : x_(x), y_(y) {
      (void) x_;
      (void) y_;
    }

  private:
    int x_;
    int y_;
};

int main() {
  auto p = point{1,2};
  //double length = p;
}