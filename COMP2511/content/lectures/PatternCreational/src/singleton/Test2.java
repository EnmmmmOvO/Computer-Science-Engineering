package singleton;

public class Test2 {

	public static void main(String[] args) {
		
        MyThread th1 = new MyThread("AAA");
        th1.start();


        MyThread th2 = new MyThread("BBB");  
        th2.start();

        (new MyThread("CCC")).start(); 
        (new MyThread("DDD")).start();         
        (new MyThread("EEE")).start(); 
	
        System.out.println(" -- End of program --");
		
	}

}
