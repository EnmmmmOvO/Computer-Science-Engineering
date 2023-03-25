package SampleInheritance;

/**
 * Demo file, it may not be correct and/or complete.  
 * Please watch the corresponding lecture(s) for more explanations.
 * 
 * @author ashesh
 *
 */

public class Test_equals {

	public static void main(String[] args) {
		
		A a1 = new A(4, 5);
		A a2 = new A(4, 5);
		
		// compares references, which are different
		System.out.println( " a1 == a2  returns: " + (a1 == a2)  );	


		if(a1.equals(a2)) {
			System.out.println(" a1.equals(a2) is True");
		}
		else {
			System.out.println(" a1.equals(a2) is False");			
		}
		
		B b1 = new B(4, 5);

		A a3 = b1; 

		System.out.println( " b1.equals(a2) returns: " + a3.equals(a2));	

		
	}

}
