package exception;

import java.io.IOException;

public class Test1 {

	public static void main(String[] args)  {

		ListOfNumbers ln = new ListOfNumbers();
		try {
			
			ln.writeList();
		} 
		catch (IOException e) {
			System.out.println(" something went wrong!!! ");
			e.printStackTrace();
		}
		catch(Exception e){
			System.out.println("Got it... !");
			e.printStackTrace();
		}

		System.out.println(" ### end of program ");
	}

}
