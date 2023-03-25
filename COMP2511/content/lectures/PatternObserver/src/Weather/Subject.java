package Weather;
/** Demo file, it may not be correct and/or complete.  
 * Please watch the corresponding lecture(s) for more explanations.
 * @author ashesh
 */

public interface Subject {

	public void attach(Observer o);
	public void detach(Observer o);
	public void notifyObservers();
	
}
