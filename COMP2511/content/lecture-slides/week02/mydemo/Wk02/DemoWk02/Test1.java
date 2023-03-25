package DemoWk02;

public class Test1 {
    

    public static void main(String[] args) {
        
        A a1 = new A();
        A a2 = new A(45, 71);

        B b1 = new B();

        System.out.println(" a1.x is " + a1.x);
        System.out.println(" a2.x is " + a2.x);
        System.out.println(" b1.x is " + b1.x);

        int val1 = a1.f();
        int val2 = b1.f();

        b1.f();

        A a3 = (A) b1; 
        int valFB = a3.f();  // <-----
        System.out.println("===================");
        a2.f();
        System.out.println("===================");

        System.out.println(a1.x + " : " + b1.x);
        System.out.println("===================");
        System.out.println(a3.x + " : " + b1.x);
        System.out.println("===================");

        b1.m1();

        System.out.println(valFB);
        




    }


}