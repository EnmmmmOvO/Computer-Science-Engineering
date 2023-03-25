package WeatherV2;
/** Demo file, it may not be correct and/or complete.  
 * Please watch the corresponding lecture(s) for more explanations.
 * @author ashesh
 */

public interface SubjectThermometer {

	public void attach(ObserverThermometer o);
	public void detach(ObserverThermometer o);
	public void notifyObservers();

	public double getTemperatureC();

	
}
