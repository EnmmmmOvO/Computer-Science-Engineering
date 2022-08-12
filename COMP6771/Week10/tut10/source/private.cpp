class base_class {
private:
	int i_;
};

class derived_class : public base_class {
public:
	auto foo(Derived& o) -> void {
    	j_ = o.i_ + o.j_;
	}
private:
	int j_;
};