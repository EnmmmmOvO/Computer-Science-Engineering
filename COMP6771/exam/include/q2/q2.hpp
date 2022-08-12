#ifndef Q2_HPP
#define Q2_HPP

namespace q2 {
    template <typename T, auto C, auto D>
    class scope_guard {
    public:
        scope_guard() noexcept {
            resource_ = std::make_unique<T>;
        }

        template <typename ...Args>
        scope_guard(Args &&...args) {
            resource_ = std::make_unique<T>;
            resource_.get() = std::copy(args.begin(), args.end(), *resource_.get());
        }
    private:
        std::unique_ptr<T> resource_;

    };
}

#endif // Q2_HPP
