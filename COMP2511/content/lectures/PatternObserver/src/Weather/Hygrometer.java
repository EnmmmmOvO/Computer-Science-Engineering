package Weather;
/** Demo file, it may not be correct and/or complete.  
 * Please watch the corresponding lecture(s) for more explanations.
 * @author ashesh
 */

import java.util.ArrayList;

public class Hygrometer implements Subject {

	ArrayList<Observer> listObservers = new ArrayList<Observer>();
	double humidity = 0.0;
	
	@Override
	public void attach(Observer o) {
		if(! listObservers.contains(o)) { listObservers.add(o); }
	};

	@Override
	public void detach(Observer o) {
		listObservers.remove(o);		
	}

	@Override
	public void notifyObservers() {
		for(Observer obs : listObservers) {
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
