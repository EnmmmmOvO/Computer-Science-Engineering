package MethodsStaticVsInstance;

public class Test1 {

	public static void main(String[] args) {

		B b1 = new B();
		b1.f1();  // From f1 in B (instance method)
		b1.f2();  // From f2 in B (static method)
		
		A a1 = b1;
		a1.f1();  // From f1 in B (instance method)
		a1.f2();  // From f2 in A (static method)
		
		
		/**
		 *  Class B overrides instance method f1() 
		 *  However, static method f2() is NOT overridden!
		 *  There are two static methods f2(), 
		 *  one for type A and another for type B
		 *  
		 * Output is
		From f1 in B (instance method)
		From f2 in B (static method)
		From f1 in B (instance method)
		From f2 in A (static method)

		 */
	}

}
