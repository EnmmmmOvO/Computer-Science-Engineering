 public class Circle extends Object {

    private static final double PI = 3.14159;

    public int x = 0, y = 0;
    private int r = 6;

    static int no_circles = 0;

    public Circle() {
        super();
        no_circles++;
    }

    public Circle(int x, int y, int r) {
        this();
        this.x = x;
        this.y = y;
        this.r = r;
  
    }


    public Circle(int x, int y) {
        this(x, y, 5);
    }

    public double getArea() {
        return PI * r * r;
    }

    @Override
    public String toString() {
        String msg = "[" + x + ", " + y + " sdfsf sdfdsfds ]";
        return msg;
    }

    @Override
    public boolean equals(Object obj) {
   
        if(obj == null) { return false; }
        if(obj == this) { return true; }

        if(this.getClass() != obj.getClass()){
            return false;
        }

        // both are of type Circle..

        Circle other = (Circle) obj;
        if(this.x == other.x && this.y == other.y && this.r == other.r){
            return true;
        }
        else {
            return false;
        }
         
    }
    
    // Getter and Setter below ..
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
        if ( r > 0 ) {
            this.r = r;
        }

    }


}