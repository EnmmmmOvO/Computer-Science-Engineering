package access.package1;

public class C {

    public void methodC() {
        // A class C in the same package as another class A
        // has access to only variables in A with default, public and protected
        // scope

        A a = new A();
        System.out.println("var: " + a.var);
        System.out.println("varPub: " + a.varPub);
        System.out.println("varPro: " + a.varPro);

        // The line below does not compile because
        // this do not have access to private variables in super class
//        System.out.println("varPriv: " + varPriv);

        // TODO Are protected and default useful access modifiers?
    }

}
