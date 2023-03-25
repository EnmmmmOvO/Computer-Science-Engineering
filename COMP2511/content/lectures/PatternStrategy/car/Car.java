package car;
/** Demo file, it may not be correct and/or complete.  
 * Please watch the corresponding lecture(s) for more explanations.
 * @author ashesh
 */

public class Car {
	protected EngineType engine ; 
	protected BrakeStrategy brake; 

	/**
	 * other fields and methods here
	 */
	
	public Car(EngineType engine, BrakeStrategy brake) {
		this.brake = brake;
		this.engine = engine;
	}
	
	/**
	 * other fields and methods here
	 */	
	
	public void brakeApply() {
		brake.apply();
	}
	
	public void engineRun() {
		engine.run();
	}
}


