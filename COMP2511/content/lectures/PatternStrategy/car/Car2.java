package car;
/** Demo file, it may not be correct and/or complete.  
 * Please watch the corresponding lecture(s) for more explanations.
 * @author ashesh
 */

public class Car2 {
	private String engine ; 
	private String brake; 

	/**
	 * other fields and methods here
	 */
	
	public Car2(String engine, String brake) {
		this.brake = brake;
		this.engine = engine;
	}
	
	/**
	 * other fields and methods here
	 */	
	
	public void brakeApply() {
		
		switch (brake) {
			case "normal" : 
				brakeNormal();
				break;
			case "abs" : 
				brakeABS();
				break;	
			case "disc" : 
				brakeDisk();
				break;	
			case "drum" : 
				brakeDrum();
				break;					
		}		
	}
	
	private void brakeDrum() {
		// TODO Auto-generated method stub
		System.out.println("Braking style is Drum ");		
		
	}

	private void brakeDisk() {
		// TODO Auto-generated method stub
		System.out.println("Braking style is Disk ");		
		
	}

	private void brakeABS() {
		// TODO Auto-generated method stub
		System.out.println("Braking style is ABS ");		
		
	}

	private void brakeNormal() {
		// TODO Auto-generated method stub
		System.out.println("Braking style is Normal ");		
		
	}


	public void engineRun() {
		
		switch (engine) {
			case "normal" : 
				engineNormal();
				break;
			case "turbo" : 
				engineTurbo();
				break;	
			case "hybrid" : 
				engineHybrid();
				break;	
			case "electric" : 
				engineElectric();
				break;	
			case "hydrogen" : 
				engineHydrogen();
				break;					
		}		
	}

	private void engineHydrogen() {
		// TODO Auto-generated method stub
		System.out.println("Engine type is Hydrogen ");		
		
	}

	private void engineElectric() {
		// TODO Auto-generated method stub
		System.out.println("Engine type is Electric ");		
		
	}

	private void engineHybrid() {
		// TODO Auto-generated method stub
		System.out.println("Engine type is Hybride ");		
		
	}

	private void engineTurbo() {
		// TODO Auto-generated method stub
		System.out.println("Engine type is Turbo ");		
		
	}

	private void engineNormal() {
		// TODO Auto-generated method stub
		System.out.println("Engine type is Normal ");		
		
	}	
}
