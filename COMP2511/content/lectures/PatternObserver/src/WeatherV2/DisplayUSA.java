package WeatherV2;
/** Demo file, it may not be correct and/or complete.  
 * Please watch the corresponding lecture(s) for more explanations.
 * @author ashesh
 */

public class DisplayUSA implements ObserverHygrometer , ObserverThermometer {
	Subject subject;
	double temperatureC = 0.0;
	double humidity = 0.0;

	@Override
	public void update(SubjectHygrometer obj) {

		this.humidity = obj.getHumidity();
		displayHumidity();
		
	}

	@Override
	public void update(SubjectThermometer obj) {
			this.temperatureC = obj.getTemperatureC();
			displayTemperature();
	}
	
	
	public void display() {
		System.out.printf("From DisplayUSA: Temperature is %.2f F, "
				+ "Humidity is %.2f\n", convertToF(), humidity);
	}

	public void displayTemperature() {
		System.out.printf("From DisplayUSA: Temperature is %.2f F\n",
				 convertToF() );
	}

	public void displayHumidity() {
		System.out.printf("From DisplayUSA: Humidity is %.2f\n", humidity);
	}

	public double convertToF() {
		return (temperatureC *(9.0/5.0) + 32);
	}
}
