/** Demo Example for COMP2511 
 * @author ashesh
 */

package composite.uniformity;

public interface Component {
	
	public String nameString();
	public double calculateCost();
	
	public boolean add(Component child);
	public boolean remove(Component child);
	
}
