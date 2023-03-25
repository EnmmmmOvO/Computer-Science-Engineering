package exception2;

import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;

public class ListOfNumbers {

	private ArrayList<Integer> list;
	private static final int SIZE = 10;

	public ListOfNumbers() {
		list = new ArrayList<Integer>();
		for (int i = 0; i < SIZE; i++) {
			int randomInt = (int) (Math.random() * 100);
			list.add(randomInt);
		}
	}

	public void writeList() {

		PrintWriter out = null;

		try {
			out = new PrintWriter(new FileWriter("myData.txt"));
			for(int i=0; i<SIZE; i++){
				out.println(list.get(i+5));
			}
			//out.close();
			//System.out.println("closing file ... 111");


		}
		catch(IOException e){
			System.out.println(" In writeln ....");
		}
		catch(Exception e){
			System.out.println(" In writeln, Exception  ....");

		}
		finally{
			System.out.println("closing file ... 222");
			out.close();
		}

	}

}
