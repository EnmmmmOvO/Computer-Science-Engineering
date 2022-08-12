#include <exception>
#include <string>
#include <iostream>

class Logger {
public:
    auto log(std::string const& msg) -> void;
};

class DBConn {
public:
    auto try_connect(std::string const& uname, std::string const& pword) -> void {
        (void) uname;
        (void) pword;
        (void) active_;
        // just a stub
    }

private:
    bool active_ = false;
};

auto make_connection(std::string const& uname, std::string const& pword) -> DBConn {
    auto db = DBConn{};
    try {
        db.try_connect(uname, pword);
    } catch (std::string const & e) {
        std::cout << e << std::endl;
    }
    return db;
}

int main() {
    auto l = Logger{};
    (void)l;
    make_connection("hsmith", "swagger/10");
}