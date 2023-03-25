package Shapes;

/**
 * Demo file, it may not be correct and/or complete.  
 * Please watch the corresponding lecture(s) for more explanations.
 * 
 * @author ashesh
 *
 */

public  abstract class Shape {

	public abstract double area();
	public abstract double circumference();

	protected static int count_shapes = 0;

	public void printArea(){
		System.out.println(" (from Shape abstract class, method printArea)> area is: " + this.area());
	}

}

