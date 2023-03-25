package car;
/** Demo file, it may not be correct and/or complete.  
 * Please watch the corresponding lecture(s) for more explanations.
 * @author ashesh
 */

public class BrakeABS implements BrakeStrategy {

	@Override
	public void apply() {
		System.out.println("Braking style is ABS ");
		
	}	

}
