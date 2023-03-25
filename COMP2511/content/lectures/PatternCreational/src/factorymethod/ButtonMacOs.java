package factorymethod;

public class ButtonMacOs implements Button {
	private String label = "";
	private String colour = "";

	
	@Override
	public String getLabel() {
		return label;
	}

	@Override
	public void setLabel(String label) {
		this.label = label;
	}

	@Override
	public void setBgColour(String colour) {
		this.colour = colour;	
	}

	@Override
	public String getBgColour() {
		return this.colour; 
	}
	
	
	@Override
	public void click() {
		System.out.println("MacOs Button is Clicked !! ");
	}

	@Override
	public String toString() {
		return "MacOs Button, lable: " + getLabel() ;
	}
}
