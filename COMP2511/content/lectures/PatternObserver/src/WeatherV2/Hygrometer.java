package WeatherV2;
/** Demo file, it may not be correct and/or complete.  
 * Please watch the corresponding lecture(s) for more explanations.
 * @author ashesh
 */

import java.util.ArrayList;

public class Hygrometer implements SubjectHygrometer {

	ArrayList<ObserverHygrometer> listObservers = new ArrayList<ObserverHygrometer>();
	double humidity = 0.0;
	
	@Override
	public void attach(ObserverHygrometer o) {
		if(! listObservers.contains(o)) { listObservers.add(o); }
	};

	@Override
	public void detach(ObserverHygrometer o) {
		listObservers.remove(o);		
	}

	@Override
	public void notifyObservers() {
		for(ObserverHygrometer obs : listObservers) {
			obs.update(this);
		}
	}

	public double getHumidity() {
		return humidity;
	}

	public void setHumidity(double humidity) {
		this.humidity = humidity;
		notifyObservers();
	}
	
	

}
