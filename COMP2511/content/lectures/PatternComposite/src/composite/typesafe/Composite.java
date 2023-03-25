/** Demo Example for COMP2511 
 * @author ashesh
 */

package composite.typesafe;

import java.util.ArrayList;

public class Composite implements Component {

	private String name; 
	private double cost;
	 
	ArrayList<Component>  children = new ArrayList<Component>();
	
	public Composite(String name, double cost) {
		super();
		this.name = name;
		this.cost = cost;
	}

	@Override
	public double calculateCost() {
		double answer = this.getCost();
		for(Component c : children) {
			answer += c.calculateCost();
		}
		
		return answer;
	}
	
	@Override
	public String nameString() {
		String answer = "[" + this.getName()  + " "; 
		for(Component c : children) {
			answer = answer + " " + c.nameString();
		}	
		answer = answer + "]";
		return answer;
	}

	public boolean add(Component child) {
		children.add(child);
		return true;
	}

	public boolean remove(Component child) {
		children.remove(child);
		return true;
	}

	// Getters and Setters below .... 

	public String getName() {
		return name;
	}

	public void setName(String name) {
		this.name = name;
	}

	public double getCost() {
		return cost;
	}

	public void setCost(double cost) {
		this.cost = cost;
	}
	
	
	
	
}
