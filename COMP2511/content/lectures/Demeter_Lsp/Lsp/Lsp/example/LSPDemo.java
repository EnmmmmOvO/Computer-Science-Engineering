package example;

public class LSPDemo {

	
	public static void main(String[] args) {
			
		//LSPDemo demo = new LSPDemo();
		
		Rectangle rect1 = new Rectangle();
		Rectangle rect2 = new Square();
		
		System.out.println(rect1.getArea());
		System.out.println(rect2.getArea());

		/**
		 * Incorrect behaviour below! 
		 */
		// Let's change width of rect2
		rect2.setWidth(10);
		
		// height of rect2 is also modified! 
		// So rect2 is NOT behaving as a rectangle, as expected by its type! 
		System.out.println("rect2 height: " + rect2.getHeight());
		
		System.out.println();
		
		
	}
	
}
