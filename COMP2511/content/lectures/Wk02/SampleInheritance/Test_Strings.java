package SampleInheritance;

/**
 * Demo file, it may not be correct and/or complete.  
 * Please watch the corresponding lecture(s) for more explanations.
 * 
 * @author ashesh
 *
 */

public class Test_Strings {

	public static void main(String[] args) {
		
		String s1 = "Sydney"; 
		String s2 = "New York";
		String s3 = "Sydney";
		
		if(s1 == s3) {
			
			System.out.println("s1 == s3 is True");
		}
		else {
			System.out.println("s1 == s3 is False");

		}
		
		String s4 = new String("Sydney");
		String s5 = new String("Sydney");
		
		if(s4 == s5) {
			
			System.out.println("s4 == s5 is True");
		}
		else {
			System.out.println("s4 == s5 is False");

		}

		System.out.println(s4.equals(s5));

		String s8 = s4.toUpperCase();
		
	
	}

}
