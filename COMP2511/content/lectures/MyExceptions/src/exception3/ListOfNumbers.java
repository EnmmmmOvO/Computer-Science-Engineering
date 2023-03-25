package exception3;

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

				int idx = i + 5;

				if(idx >= SIZE){
					throw new MyException("idx is out of index range!");
				}
				out.println(list.get(idx));
			}

		}
		catch(IOException e){
			System.out.println(" In writeln ....");
		}
		catch(MyException e){
			System.out.println(e.getMessage());
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
