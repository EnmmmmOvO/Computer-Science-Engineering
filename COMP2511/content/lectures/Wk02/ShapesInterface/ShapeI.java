package ShapesInterface;

public interface ShapeI {

	public double area();
	public double circumference();    

    default public void printArea() {
        System.out.println(" (from ShapeI interface, default method printArea)> area is: " + this.area());
    } 
    
}