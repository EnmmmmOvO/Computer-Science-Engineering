package SampleInheritance;

/**
 * Demo file, it may not be correct and/or complete.  
 * Please watch the corresponding lecture(s) for more explanations.
 * 
 * @author ashesh
 *
 */

public class Test1 {

	public static void main(String[] args) {

		A a1 = new A(4, 8);
		
		B b1 = new B(2, 1, 5);
		
		B b2 = new B();
		//b2.m1();
		b2.f();
		
		A a3 = b2; 
		a3.f();
		
		B b5 = (B) a3; 
		
		b5.f();
		
		System.out.println(b2);
		
		a1 = new A(3,5);
		A a2 = new A(3,5);
		
		if( a1.equals(a2)) {
			System.out.println("Same");
		}
		else {
			System.out.println("Not Same");			
		}
		
		System.out.println(" ----- -------- ");
		b1 = new B();
		a2 =  b1; 
		System.out.println(a2.x + " : " + b1.x);
		
		System.out.println(" ----- -------- ");		
		b1.f();
		System.out.println(" ----- -------- ");		
		a2.f();
		
		
		
	}

}
