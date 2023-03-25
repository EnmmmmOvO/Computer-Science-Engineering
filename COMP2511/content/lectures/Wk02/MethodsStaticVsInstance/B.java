package MethodsStaticVsInstance;

public class B extends A {

	public void f1() {
		System.out.println("From f1 in B (instance method)");
	}

	public static void f2() {
		System.out.println("From f2 in B (static method)");
	}
	
}
