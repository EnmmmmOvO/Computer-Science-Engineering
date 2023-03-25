package exception;

import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;

public class ListOfNumbers {

	private final ArrayList<Integer> list;
	private static final int SIZE = 10;

	public ListOfNumbers() {
		list = new ArrayList<Integer>();
		for (int i = 0; i < SIZE; i++) {
			final int randomInt = (int) (Math.random() * 100);
			list.add(randomInt);
		}
	}

	public void writeList() throws IOException {
		PrintWriter out = null;


		out = new PrintWriter(new FileWriter("myData.txt"));

		for (int i = 0; i < SIZE; i++) {
			out.println("Value is " + list.get(i+5));
		}

		out.close();
	}

}
