/** Demo Example for COMP2511 
 * @author ashesh
 */

package composite.typesafe;

public class Test2 {

	public static void main(String[] args) {

		Composite mainboard = new Composite("Mainboard", 100);
		Leaf processor = new Leaf("Processor", 450);
		Leaf memory    = new Leaf("Memory", 80);
		mainboard.add(processor);
		mainboard.add(memory);
		
		
		Composite chasis = new Composite("Chasis", 75);
		chasis.add(mainboard);

		Component disk = new Leaf("Disk", 50);
		chasis.add(disk);
		
		
		System.out.println("[0] "+ processor.nameString());
		System.out.println("[0] "+ processor.calculateCost());
		

		System.out.println("[1] "+ mainboard.nameString());
		System.out.println("[1] "+ mainboard.calculateCost());
		

		System.out.println("[2] "+ chasis.nameString());
		System.out.println("[2] "+ chasis.calculateCost());
		
		
		
		
		
	}

}
