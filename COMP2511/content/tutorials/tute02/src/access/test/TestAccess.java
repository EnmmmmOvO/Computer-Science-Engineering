package access.test;

// Classes A,B,C and D need to be imported as they live in a different package to TestAccess
import access.package1.A;
import access.package1.B;
import access.package1.C;
import access.package2.D;

public class TestAccess {
	
	public static void main(String[] args) {
		
		A objA = new A();
		objA.methodA();  	
	    System.out.println("---");
		B objB = new B();
		objB.methodB();
	    System.out.println("---");		
		C objC = new C();
		objC.methodC();
	    System.out.println("---");
		D objD = new D();
		objD.methodD();
	}
}
