package singleton;

import java.time.LocalTime;

public class MySingleton2 {

	private static MySingleton2 single_instance = null ;
    private static int count = 0;

	private LocalTime localTime;

	private MySingleton2() {
		localTime = LocalTime.now();
	}

	public static synchronized MySingleton2 getInstance() {
		if (single_instance == null) {

		    System.out.println("Inside IF, time: " + LocalTime.now());

			// let's sleep for 3 seconds .. ! 
			try {
				Thread.sleep(3000);
			} catch (InterruptedException ex) {
				ex.printStackTrace();
			}

			single_instance = new MySingleton2();
            count++;

		    System.out.println(count + ": after new  MySingleton2(), time: " + LocalTime.now());

		}
        else{
		    System.out.println(count + ": single_instance not null, time: " + LocalTime.now());            
        }
		
		return single_instance;
	}

	public LocalTime getTime() {
		return localTime;
	}
}
