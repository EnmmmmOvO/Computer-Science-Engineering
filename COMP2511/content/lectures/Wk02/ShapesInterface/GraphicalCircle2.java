package ShapesInterface;

import java.awt.Color;
import java.awt.Graphics;

/**
 * Demo file, it may not be correct and/or complete. Please watch the
 * corresponding lecture(s) for more explanations.
 * 
 * @author ashesh
 *
 */

public class GraphicalCircle2 implements ShapeI {
	// here's the math circle
	Circle c;
	// The new graphics variables go here
	Color outline, fill;

	// Very simple constructor
	public GraphicalCircle2() {
		c = new Circle();
		this.outline = Color.black;
		this.fill = Color.white;
	}

	// Another simple constructor
	public GraphicalCircle2(int x, int y, int r, 
							Color o, Color f) {
		c = new Circle(x, y, r);
		this.outline = o;
		this.fill = f;
	}

	// draw method , using object 'c'
	public void draw(Graphics g) {
		g.setColor(outline);
		g.drawOval(c.x - c.r, c.y - c.r, 2 * c.r, 2 * c.r);
		g.setColor(fill);
		g.fillOval(c.x - c.r, c.y - c.r, 2 * c.r, 2 * c.r);
	}
	

	// Here are the old methods
	public double area() {
		return c.area();
	}

	public double circumference() {
		return c.circumference();
	}


    @Override
    public boolean equals(Object obj) {

        if(obj == null ) { return false;}
        if(this.getClass() != obj.getClass()){
            return false;
        }

        GraphicalCircle2 other = (GraphicalCircle2) obj;
        if( this.c.equals(other.c) && 
			other.fill.equals(this.fill)  && 
			other.outline.equals(this.outline)  ){

            return true;
        }
        else{
            return false;
        }
    }


}
