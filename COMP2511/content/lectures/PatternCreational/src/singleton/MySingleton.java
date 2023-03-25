package singleton;

import java.time.LocalTime;

public class MySingleton {

	private static MySingleton single_instance = null ;
	private static String  db = null;

	private LocalTime localTime;

	private MySingleton() {
		localTime = LocalTime.now();
		/**
		 * code to create db connection
		 * String db = ???
		 * 
		 */		
	}

	public static synchronized MySingleton getInstance() {
		if (single_instance == null) {

			single_instance = new MySingleton();
		}
		return single_instance;
	}

	public LocalTime getTime() {
		return localTime;
	}
}
