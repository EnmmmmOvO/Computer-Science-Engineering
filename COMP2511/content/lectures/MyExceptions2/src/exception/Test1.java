package exception;

public class Test1 {

	public static void main(String[] args)  {

		try {
			ListOfNumbers ln = new ListOfNumbers();
			ln.writeList();
		}
		catch(MyException1 e) {
			System.out.println(e.getMessage());
			//e.printStackTrace();
		} catch (MyException5 e) {
			e.printStackTrace();
		}
	}

}
