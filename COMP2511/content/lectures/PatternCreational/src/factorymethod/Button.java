package factorymethod;

public interface Button {
	
	public void setLabel(String label);
	public String getLabel();

	public void setBgColour(String colour);
	public String getBgColour();
	
	public void click();

}
