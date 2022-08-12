class A {
 public:
  virtual void f(int) {}
  virtual int g() {}
  void a() {}
  virtual ~A() {}
};

class B : public A {
 public:
  void f(int) override {}
  virtual int h() {}
};

class C : public B {
 public:
  virtual void f(int, int) {}
  virtual void x() {}
  static void b() {}
};
