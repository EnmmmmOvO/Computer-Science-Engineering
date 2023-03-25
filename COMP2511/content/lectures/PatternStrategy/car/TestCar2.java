package car;
/** Demo file, it may not be correct and/or complete.  
 * Please watch the corresponding lecture(s) for more explanations.
 * @author ashesh
 */

public class TestCar2 {

	public static void main(String[] args) {
		// TODO Auto-generated method stub
		
		Car2 c1 = new Car2("normal", "abs");
		c1.brakeApply();
		c1.engineRun();
		System.out.println("--------------- ");
		
		Car2 c2 = new Car2("turbo", "drum");
		c2.brakeApply();
		c2.engineRun();

		
	}

}
