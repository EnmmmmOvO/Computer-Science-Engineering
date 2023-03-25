package factorymethod;

public class ButtonWin10 implements Button {
	private String label = "No Label!";
	private String colour = "Black";

	
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
		System.out.println("Win10 Button is Clicked !! ");
	}

	@Override
	public String toString() {
		return "Win10 Button, lable: " + getLabel() ;
	}

	
	
}
