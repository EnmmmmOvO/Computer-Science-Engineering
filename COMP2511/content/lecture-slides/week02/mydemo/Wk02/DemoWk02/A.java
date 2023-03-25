package DemoWk02;

public class A {

    int x = 25;
    int y = 2;

    public A() {
        super();
    }

    public A(int x, int y) {
        this.x = x;
        this.y = y;
    }

    public int f() {

        System.out.println("In class A, method f");
        System.out.println("   > x is " + x);
        System.out.println("   > y is " + y);

        return x + y;
    }

    public double myAdd(int a, int b) {
        return a + b;
    }

    public double myAdd(double a, double b) {
        return a + b;
    }

    public double myAdd(String a, String b) {
        double d1 = Double.parseDouble(a);
        double d2 = Double.parseDouble(a);

        return d1 + d2;
    }

    @Override
    public boolean equals(Object obj) {

        if(obj == null ) { return false;}
        if(this.getClass() != obj.getClass()){
            return false;
        }

        A other = (A) obj;
        if(other.x == this.x && other.y == this.y){
            return true;
        }
        else{
            return false;
        }
    }
    
    


}