package ShapesInterface;

import java.awt.Color;
import java.awt.Graphics;

/**
 * Demo file, it may not be correct and/or complete. Please watch the
 * corresponding lecture(s) for more explanations.
 * 
 * GraphicalCircle - to demonstrate inheritance
 * 
 * @author ashesh
 *
 */

public class GraphicalCircle extends Circle {

	Color outline, fill;

	/**
	 * No-arg constructor for GraphicalCircle
	 */
	public GraphicalCircle() {
		// First call no-arg constructor from the super class Circle
		super();
		//Set additional values for this sub-class
		this.outline = Color.black;
		this.fill = Color.white;
		x = 70;
	}

	/**
	 * 5 arg constructor for GraphicalCircle
	 * 
	 * @param x x axis
	 * @param y y axis
	 * @param r radius
	 * @param o outline color
	 * @param f fill color
	 */
	public GraphicalCircle(int x, int y, int r, Color o, Color f) {
		super(x, y, r); // call 3-arg constructor from Circle
		this.outline = o;
		this.fill = f;
	}

	public void draw(Graphics g) {
		g.setColor(outline);
		g.drawOval(x - r, y - r, 2 * r, 2 * r);
		g.setColor(fill);
		g.fillOval(x - r, y - r, 2 * r, 2 * r);
	}

	@Override
    public boolean equals(Object obj) {

        if(super.equals(obj) == false) { return false;} 

        GraphicalCircle other = (GraphicalCircle) obj;
		if(  other.outline.equals(this.outline) && 
		     other.fill.equals(this.fill)     )  {

            return true;
        }
        else{
            return false;
		}
	}

}
