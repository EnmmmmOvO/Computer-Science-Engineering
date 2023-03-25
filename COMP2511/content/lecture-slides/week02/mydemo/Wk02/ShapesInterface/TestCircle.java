package ShapesInterface;

import java.awt.Color;
import java.util.ArrayList;

/**
 * Demo file, it may not be correct and/or complete.  
 * Please watch the corresponding lecture(s) for more explanations.
 * 
 * @author ashesh
 *
 */

public class TestCircle {
	

	public static void main(String[] args) {

		Circle c1 = new Circle(2, 2, 4); 
		System.out.println("c1 area is: " + c1.area());

		Circle c2 = new Circle(5, 1, 3); 
		System.out.println("c2 area is: " +c2.area());		

		Circle c3 = new GraphicalCircle(); 
		System.out.println("c3 area is: " +c3.area());	

		Circle c4 = new GraphicalCircle(3, 2, 4, Color.blue, Color.green); 
		System.out.println("c4 area is: " + c4.area());	

		/**
		 * Class variable, "Circle.count_circle" 
		 */
		System.out.println("Circle.count_circle : " + Circle.count_circle);	

		/**
		 *  Methods Overriding, 
		 *  Polymorphism Example
		 */
		// create an array to hold shapes
		ArrayList<ShapeI> shapes = new ArrayList<ShapeI>();

		shapes.add(new Circle(4, 6, 2));
		shapes.add(new Rectangle(1.0, 3.0));
		shapes.add(new Rectangle(4.0, 2.0));
		shapes.add(new GraphicalCircle(1, 1, 6, 
					    Color.green, Color.yellow));
		shapes.add(new GraphicalCircle(5, 3, 4, 
						Color.green, Color.yellow));
						

		int count_circle = 0;
		double total_area = 0;
		int onlyCircleClass_count = 0;

		for(int i = 0; i < shapes.size(); i++) {
			
			// Compute the area of the shapes using
			// polymorphism (behaviour) below.
			
			total_area += shapes.get(i).area();    
			
			// instanceof will match objects of types Circle and its subclasses (like GraphicalCircle)
			if(shapes.get(i) instanceof Circle ) {
				count_circle++;
			}

			// the following will only match objects of type Circle
			if(shapes.get(i).getClass() == Circle.class){
				onlyCircleClass_count++;
			}
			
		} 						       		  

		System.out.println("total_area is: " + total_area );
		System.out.println("count_circle is: " + count_circle );
		System.out.println("onlyCircle_count is: " + onlyCircleClass_count );

		
		/**
		 * Class variable "Circle.count_circle" 
		 */
		System.out.println("Circle.count_circle : " + Circle.count_circle);	

		/**
		 * Casting example
		 * if shapeTemp is an instance of class Circle, 
		 * cast it to Circle, and call the instance method getR().
		 */
		ShapeI shapeTemp = shapes.get(0); 
		
		/* Use of "instanceof"
		 * 
		 * Let's check if an object (shapeTemp) of type ShapeI is also 
		 * an instance-of Circle, if yes, cast it to Circle and print radius
		 */
		if( shapeTemp instanceof Circle ) {
			
			// cast shapes[0] to Circle class
			Circle cTemp = (Circle) shapeTemp; 
			
			// call the instance method getR from the class Circle
			System.out.println(  "(1) Radius is:" + cTemp.getR()   )  ;
			
			// Or use the following one-liner ... 
			System.out.println(  "(2) Radius is:" + ( (Circle) shapes.get(0) ).getR()   )  ;
		}

		/** 
		 * Let's print area using the method "printArea" implemented 
		 * in  the abstract class "Shape"
		 * */ 

		for(ShapeI s : shapes){
			s.printArea();
		}
		
	}
	
	
}
