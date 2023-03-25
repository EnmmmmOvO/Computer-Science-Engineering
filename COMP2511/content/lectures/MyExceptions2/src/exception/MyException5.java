package exception;

public class MyException5 extends Exception {

    private static final long serialVersionUID = 1L;
    
	private String message;
	
	public MyException5(String message) {
		this.message = message;
	}
	
	public String getMessage() {
		return message;
	}    
}