package access.package2;

import access.package1.A;

public class D {

    public void methodD() {
        // A class D in another package to a class A has only access to
        // variables in A with public scope

        A objA = new A();
        // The line below does not compile because variables with scope default
        // are only visible to classes in the same package
//        System.out.println("var: " + objA.var);
        System.out.println("varPub: " + objA.varPub);

        // The line below does not compile because variables with scope
        // protected are only visible to classes in the same package or
        // sub-classes
//        System.out.println("varPro: " + objA.varPro);

        // The line below does not compile because this class does not have
        // access to private variables in super class
//        System.out.println("varPriv: " + varPriv);
    }
}
