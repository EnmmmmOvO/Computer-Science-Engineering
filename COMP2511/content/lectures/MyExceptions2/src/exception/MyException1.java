package exception;

public class MyException1 extends Exception {

	private static final long serialVersionUID = 1L;
	
	private String message;
	
	public MyException1(String message) {
		this.message = message;
	}
	
	public String getMessage() {
		return message;
	}
	
}
