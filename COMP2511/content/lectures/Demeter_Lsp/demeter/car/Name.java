/**
 * Demo file, it may not be correct and/or complete.  
 * Please watch the corresponding lecture(s) for more explanations.
 * 
 * @author ashesh
 */

package car;

public class Name {
	
	private String firstName;
	private String lastName;
	
	public Name(String firstName, String lastName) {
		super();
		this.firstName = firstName;
		this.lastName = lastName;
	}
	
	public String getFirstName() {
		return firstName;
	}
	public void setFirstName(String firstName) {
		this.firstName = firstName;
	}
	public String getLastName() {
		return lastName;
	}
	public void setLastName(String lastName) {
		this.lastName = lastName;
	}
	
}
