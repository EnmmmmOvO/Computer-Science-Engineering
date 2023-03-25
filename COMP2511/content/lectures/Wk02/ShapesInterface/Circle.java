package ShapesInterface;


/**
 * Demo file, it may not be correct and/or complete.  
 * Please watch the corresponding lecture(s) for more explanations.
 * Circle class.
 * 
 * @author ashesh
 *
 */

public class Circle  implements ShapeI {

	protected static final double pi = 3.14159; 
	int  x, y;
	protected  int  r;
	protected static int count_circle = 0;

	/**
	 * No-arg constructor
	 */
	public Circle(){
		this.x = 1;
		this.y = 1;
		this.r = 1;

		count_circle++; 	
	}
	
	public Circle(int r){
		this();
		this.r = r;
	}
	
	/**
	 * Constructor with 2 args 
	 * @param x x axis
	 * @param y y axis
	 */
	public Circle(int x, int y){
		this.setX(x);
		this.setY(y);

		count_circle++; 
	}	
	
	/**
	 * Constructor with 3 args 
	 * @param x x axis
	 * @param y y axis
	 * @param r radius 
	 */
	public Circle(int x, int y, int r)  {
		// First call the constructor Circle(int x, int y)
		// from this class
		this(x,y);   
		
		// Now set r
		this.setR(r);

	}

	/**
	 * The method returns circumference of the circle
	 * @return circumference of the circle
	 */
	public double  circumference( ) {  
		return 2 * pi * r ; 
	}

	/**
	 * The method returns area of the circle
	 * @return  area of the circle
	 */
	public  double  area ( ) {
		return  pi * r * r ; 
	}
	
	public int getX() {
		return x;
	}
	public void setX(int x) {
		this.x = x;
	}
	public int getY() {
		return y;
	}
	public void setY(int y) {
		this.y = y;
	}
	public int getR() {
		return r;
	}
	public void setR(int r) {
		this.r = r;
	}

    @Override
    public boolean equals(Object obj) {

        if(obj == null ) { return false;}
        if(this.getClass() != obj.getClass()){
            return false;
        }

        Circle other = (Circle) obj;
        if(other.x == this.x && other.y == this.y && other.r == this.r){
            return true;
        }
        else{
            return false;
        }
    }
		
}
