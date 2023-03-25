package WeatherV2;
/** Demo file, it may not be correct and/or complete.  
 * Please watch the corresponding lecture(s) for more explanations.
 * @author ashesh
 */

public class DisplayAustralia implements ObserverThermometer {
	Subject subject;
	double temperatureC = 0.0;
	
	
	@Override
	public void update(SubjectThermometer obj) {

			this.temperatureC =  obj.getTemperatureC();
			display();
	}

	public void display() {
		System.out.printf("From DisplayAus: Temperature is %.2f C\n", temperatureC);
	}


	
	
}
