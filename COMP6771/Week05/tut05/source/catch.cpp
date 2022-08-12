#include <algorithm>
#include <iostream>
#include <vector>

class GObject {
public:
    auto id() const { return id_; }

    auto draw() const -> void {
        if (id() == -1) {
            throw *this;
        }
        // render...
    }

private:
    int id_;
    std::vector<double> skeleton_;  // 200KB skeleton
    std::vector<double> mesh_;      // 1MB mesh
};

auto render(std::vector<GObject> const& objs) -> void {
    try {
        std::for_each(objs.begin(), objs.end(), [](auto const& o){
            o.draw();
        });
    } catch (GObject o) {
        std::cout << "Could not render" << o.id() << std::endl;
    }
}

int main() {
    render({});
}