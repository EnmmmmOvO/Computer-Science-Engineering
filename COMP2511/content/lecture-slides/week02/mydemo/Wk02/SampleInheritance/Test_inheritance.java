package SampleInheritance;

/**
 * Demo file, it may not be correct and/or complete.  
 * Please watch the corresponding lecture(s) for more explanations.
 * 
 * @author ashesh
 *
 */

public class Test_inheritance {

	public static void main(String[] args) {

		A a1 = new A();
		int val1 = a1.f(); 
		System.out.println("a1.f() returns: " + val1);
		System.out.println("----------------  ----------------  ----------------");
		
		B b1 = new B();
		int val2 = b1.f();
		System.out.println("b1.f() returns: " + val2);
		System.out.println("----------------  ----------------  ----------------");

		int val3 = b1.myAdd(4, 30);
		System.out.println("b1.myAdd(4, 30) returns: " + val3);
		System.out.println("----------------  ----------------  ----------------");

		int val4 = b1.myAdd("12", "76");
		System.out.println("b1.myAdd(\"12\", \"76\") returns: " + val4);
		System.out.println("----------------  ----------------  ----------------");
		
		int val5 = a1.myAdd(6, 20);
		System.out.println("a1.myAdd(6, 20) returns: " + val5);
		System.out.println("----------------  ----------------  ----------------");		
		
		A a2 = b1; 
		int val6 = a2.myAdd(6, 20);
		System.out.println("a2.myAdd(6, 20) returns: " + val6);
		System.out.println("----------------  ----------------  ----------------");			

		double val7 = b1.myAdd(6, 20.0);
		System.out.println("b1.myAdd(6, 20.0) returns: " + val7);
		System.out.println("----------------  ----------------  ----------------");	
		
		 
		System.out.println("b1.y is: " + b1.y);
		System.out.println("----------------  ----------------  ----------------");			

		System.out.println("a2.y is: " + a2.y);
		System.out.println("----------------  ----------------  ----------------");	

	}

}
