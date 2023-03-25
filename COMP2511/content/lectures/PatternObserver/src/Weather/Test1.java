package Weather;
/** Demo file, it may not be correct and/or complete.  
 * Please watch the corresponding lecture(s) for more explanations.
 * @author ashesh
 */

public class Test1 {

	public static void main(String[] args) {

		Thermometer thermo = new Thermometer();
		Observer usaDisplay = new DisplayUSA();
		thermo.attach(usaDisplay);

		Observer ausDisplay = new DisplayAustralia();
		thermo.attach(ausDisplay);

		System.out.println("\n----------------- thermo.setTemperatureC(30) ------------ ");		
		thermo.setTemperatureC(30);
		System.out.println("\n----------------- thermo.setTemperatureC(12) ------------ ");		
		thermo.setTemperatureC(12);



		Hygrometer hyg = new Hygrometer();
		hyg.attach(usaDisplay);
		
		System.out.println("\n----------------- hyg.setHumidity(77) ------------ ");		
		hyg.setHumidity(77);
		System.out.println("\n----------------- hyg.setHumidity(96) ------------ ");		
		hyg.setHumidity(96);
		System.out.println("\n----------------- thermo.setTemperatureC(35) ------------ ");
		thermo.setTemperatureC(35);
		

		thermo.detach(usaDisplay);
		System.out.println("\n----------------- thermo.removeObserver(usaDisplay)  ------------ ");

		System.out.println("\n----------------- thermo.setTemperatureC(41) ------------ ");
		thermo.setTemperatureC(41);
		System.out.println("\n----------------- ------------ ");
	
	}

}

