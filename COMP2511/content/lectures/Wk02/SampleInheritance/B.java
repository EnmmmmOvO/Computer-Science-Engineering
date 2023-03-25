package SampleInheritance;

/**
 * Demo file, it may not be correct and/or complete. Please watch the
 * corresponding lecture(s) for more explanations.
 * 
 * @author ashesh
 *
 */

public class B extends A {
	int x = 5;
	int y = 10;
	int z = 7;

	public B() {

	}

	public B(int x, int y, int z) {
		super();
		this.x = x;
		this.y = y;
		this.z = z;
	}

	public B(int x, int y) {
		this(x, y, 10);
	}


	public int f() {
		super.x = 100;

		System.out.println("In Class B, Method f: ");
		System.out.println(">   x is " + x + " and y is " + y);

		int val1 = super.f();
		System.out.println("In Class B, Method f: ");
		System.out.println(">   super.x is " + super.x + " and super.f() is " + val1);

		return val1 + z;
	}

	public int myAdd(int a, int b) {

		return a + b + 500;
	}

	public double myAdd(int a, double b) {

		return a + b + 2000;
	}

	@Override
	public String toString() {

		String str = "[ x: " + x + ", y: " + y + ", z: " + z + "]";
		return str;
	}

	@Override
	public boolean equals(Object obj) {
		if(super.equals(obj) == false) { return false;}

		B other = (B) obj;
		if(other.z == this.z){
			return true;
		}
		else {
			return false;
		}
	}
	
}
