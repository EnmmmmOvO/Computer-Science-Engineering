/** Demo Example for COMP2511 
 * @author ashesh
 */

package composite.typesafe;

public class Leaf implements Component {

	private String name; 
	private double cost;
	
	
	public Leaf(String name, double cost) {
		super();
		this.name = name;
		this.cost = cost;
	}

	@Override
	public String nameString() {
		return this.name;
	}

	@Override
	public double calculateCost() {
		return this.cost;
	}

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
