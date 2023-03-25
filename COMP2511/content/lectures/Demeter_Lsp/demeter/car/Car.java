/**
 * Demo file, it may not be correct and/or complete.  
 * Please watch the corresponding lecture(s) for more explanations.
 * 
 * @author ashesh
 */

package car;

public class Car {

    private  Person owner;
    
    public Car(Person owner) {
    	this.owner = owner; 
    }
    
    public Person getOwner() {
        return owner;
    }

	public void setOwner(Person owner) {
		this.owner = owner;
	}
    
}
