package example;

public class O {
	
	private Friend instanceVar = new Friend();
	
	public void M1() {
		// Invoking a method in the same class
		this.N();
	}	
	
	public void N() {
		// do something
	}
	
	public void M2(Friend f) {
		// Invoking a method on a parameter passed to the method is legal
		f.N();
	}
	
	public void M3() {
		Friend f = new Friend();
		// Invoking a method on an object created within the method is legal  
		f.N();
	}
	
	public void M4() {
		// Any method can access the methods of the friend class F through the instance variable "instanceVar" 
		instanceVar.N();
	}
	
	
	
}
