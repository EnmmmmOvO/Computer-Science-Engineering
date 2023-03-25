package example;

/*
 * Rectangle
 */
public class Rectangle {
	
	private int height;
    private int width;
     
    public int getHeight() {
        return height;
    }
    public void setWidth(int width) {
        this.width = width;
    }
    public int getWidth() {
        return width;
    }
    public void setHeight(int height) {
        this.height = height;
    }   
    public int getArea() {
        return this.height * this.width;
    }
}
