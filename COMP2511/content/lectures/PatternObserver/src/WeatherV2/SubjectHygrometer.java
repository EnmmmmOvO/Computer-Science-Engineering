package WeatherV2;
/** Demo file, it may not be correct and/or complete.  
 * Please watch the corresponding lecture(s) for more explanations.
 * @author ashesh
 */

public interface SubjectHygrometer {

	public void attach(ObserverHygrometer o);
	public void detach(ObserverHygrometer o);
	public void notifyObservers();
	
	public double getHumidity();
	
}
