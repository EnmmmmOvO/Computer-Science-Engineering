package access.package2;

import access.package1.A;

public class E extends A {

    public void methodE() {
        // Subclasses in a different package can access public and protected
        // members.
        System.out.println("varPub: " + varPub);
        System.out.println("varPro: " + varPro);

        // Even if it's another instance of E
        E e = new E();
        System.out.println("varPub: " + e.varPub);
        System.out.println("varPro: " + e.varPro);

        A a = new A();
        System.out.println("varPub: " + a.varPub);
        // TODO Does the following line compile if uncommented?
//        System.out.println("varPro: " + a.varPro);
    }
}
