package DemoWk02;

public class B extends A {

    int x = 5;
    int y = 10;
    int z = 88;


    public B() {
        super();
    }

    public void m1() {
        System.out.println("In class B,  x is " + x);
        super.f();
    }

    public int f() {
        System.out.println("In class B, method f");
        System.out.println("   > x is " + x);
        System.out.println("   > y is " + y);

        return x + y + z;
    }

    @Override
    public boolean equals(Object obj) {

        if(super.equals(obj) == false) { return false;} 

        B other = (B) obj;
        if(other.z == this.z){
            return true;
        }
        else{
            return false;
        }

    }


    
}