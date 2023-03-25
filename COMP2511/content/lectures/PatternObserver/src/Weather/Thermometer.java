package Weather;
/** Demo file, it may not be correct and/or complete.  
 * Please watch the corresponding lecture(s) for more explanations.
 * @author ashesh
 */

import java.util.ArrayList;

public class Thermometer implements Subject {
	
	ArrayList<Observer> listObservers = new ArrayList<Observer>();
	double temperatureC = 0.0;
	
	@Override
	public void attach(Observer o) {
		if(! listObservers.contains(o)) { listObservers.add(o); }
	}

	@Override
	public void detach(Observer o) {
		listObservers.remove(o);
	}

	@Override
	public void notifyObservers() {
		for( Observer obs : listObservers) {
			obs.update(this);
		}
	}

	public double getTemperatureC() {
		return temperatureC;
	}

	public void setTemperatureC(double temperatureC) {
		this.temperatureC = temperatureC;
		notifyObservers();
	}
}
