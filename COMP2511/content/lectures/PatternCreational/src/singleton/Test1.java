package singleton;

import java.time.LocalTime;

public class Test1 {

	public static void main(String[] args) {
		
		MySingleton s1 = MySingleton.getInstance();
		
		System.out.println("s1.getTime() " + s1.getTime());

		// let's sleep for 3 seconds .. ! 
        try {
            Thread.sleep(3000);
        } catch (InterruptedException ex) {
            ex.printStackTrace();
        }
        
        // display new time ... 
		System.out.println("Local time now: " + LocalTime.now());

		MySingleton s2 = MySingleton.getInstance();
		
		// same instance is returned, so the time is not changed
		System.out.println("s2.getTime() " + s2.getTime());		
		
	}

}
