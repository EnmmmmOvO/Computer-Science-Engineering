package access.package1;

/**
 * @author Aarthi A class defining variables with different access modifiers
 */
public class A {
    int var = 10;
    public int varPub = 20;
    protected int varPro = 30;
    private int varPriv = 40;

    public void methodA() {
        // Within same class, have access to all variables (default,
        // private,public,protected)
        System.out.println("var: " + var);
        System.out.println("varPub: " + varPub);
        System.out.println("varPro: " + varPro);
        System.out.println("varPriv: " + varPriv);

        A a = new A();
        // TODO Which of the following lines, when uncommented, will compile?
//        System.out.println("var: " + a.var);
//        System.out.println("varPro: " + a.varPro);
//        System.out.println("varPriv: " + a.varPriv);
    }

    protected void protectedMethod() {
        System.out.println("This method is protected.");
    }

}
