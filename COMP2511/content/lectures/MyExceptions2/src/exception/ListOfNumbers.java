package exception;

//Note: This class will not compile yet.
import java.io.*;
import java.util.List;
import java.util.Scanner;
import java.util.ArrayList;

public class ListOfNumbers {

	private List<Integer> list;
	private static final int SIZE = 10;

	public ListOfNumbers() {

		list = new ArrayList<Integer>(SIZE);
		for (int i = 0; i < SIZE; i++) {
			list.add(  (int) (Math.random() * 100) );
		}
	}

	public void writeList1() throws IOException {
		// The FileWriter constructor throws IOException, which must be caught.
		PrintWriter out;

		out = new PrintWriter(new FileWriter("OutFile.txt"));
		for (int i = 0; i < SIZE; i++) {
			// The get(int) method throws IndexOutOfBoundsException, which must be caught.
			out.println("Value at: " + i + " = " + list.get(i));
		}
		out.close();

	}

	public void writeList() throws MyException1, MyException5 {
		PrintWriter out = null;

		try {
			System.out.println("Entering" + " try statement");

			out = new PrintWriter(new FileWriter("OutFile.txt"));
			for (int i = 0; i < SIZE; i++) {
				out.println("Value at: " + i + " = " + list.get(i));
			}
			int val = 5 + 10;
			if (val > 10) {
				throw new MyException1("Val > 10 throwing our custom exception!!! ");
			}
			else if (val > 5) {
				throw new MyException5(" Val > 5 throwing our custom exception!!! ");
			}

		} catch (IndexOutOfBoundsException e) {
			System.err.println("Caught IndexOutOfBoundsException: " + e.getMessage());

		} catch (IOException e) {
			System.err.println("Caught IOException: " + e.getMessage());

		} finally {
			if (out != null) {
				System.out.println("Closing PrintWriter");
				out.close();
			} else {
				System.out.println("PrintWriter not open");
			}
		}
	}

	public void readFile() {

		try {
			File fl = new File("OutFile.txt");
			//File fl = new File("MyDaya.txt"); // throws exception, no file

			Scanner flScanner;
			flScanner = new Scanner(fl);
			while (flScanner.hasNextLine()) {
				String data = flScanner.nextLine();
				System.out.println(data);
			}
			flScanner.close();

		} catch (FileNotFoundException e) {
			e.printStackTrace();
		}

	}
	
}
