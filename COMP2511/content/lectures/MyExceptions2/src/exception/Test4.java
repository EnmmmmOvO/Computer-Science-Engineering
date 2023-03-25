package exception;

import java.io.IOException;

public class Test4 {

	public static void main(String[] args) throws IOException {
		
		ListOfNumbers ln = new ListOfNumbers();
		ln.writeList1();
		
		ln.readFile();

	}
	

}
