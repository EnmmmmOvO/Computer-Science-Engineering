package ShapesInterface;

/**
 * Demo file, it may not be correct and/or complete.  
 * Please watch the corresponding lecture(s) for more explanations.
 * 
 * @author ashesh
 * @version 1.0
 *
 */

public class Rectangle implements ShapeI {

	protected double width, height;

	/**
	 * No-arg constructor for Rectangle
	 */
	public Rectangle() {
		width = 1.0; 
		height = 1.0;

	}

	/**
	 * 2-arg constructor for Rectangle
	 * @param w width
	 * @param h height
	 */
	public Rectangle(double w, double h) { 
	
		this.width = w; 
		this.height = h; 

	}

	/**
	 * The method calculates area of the rectangle;
	 * @return double area of the rectangle
	 */
	public double area(){ 
		return width*height;
	}

	/**
	 * The method calculates circumference of the rectangle;
	 * @return double circumference of the rectangle
	 */
	public double circumference() { 
		return 2*(width + height);
	}

	/**
	 * The method returns width of the rectangle;
	 * @return width of the rectangle
	 */
	public double getWidth() {
		return width;
	}

	/**
	 * The method sets width of the rectangle;
	 * @param width new width to set
	 * @return void 
	 */
	public void setWidth(double width) {
		this.width = width;
	}

	/**
	 * The method returns height of the rectangle;
	 * @return height of the rectangle
	 */
	public double getHeight() {
		return height;
	}

	/**
	 * The method sets height of the rectangle;
	 * @param height
	 */
	public void setHeight(double height) {
		this.height = height;
	}

    @Override
    public boolean equals(Object obj) {

        if(obj == null ) { return false;}
        if(this.getClass() != obj.getClass()){
            return false;
        }

        Rectangle other = (Rectangle) obj;
		if(other.width == this.width && 
		   other.height == this.height ){
			   
            return true;
        }
        else{
            return false;
        }
    }
	
	
}


