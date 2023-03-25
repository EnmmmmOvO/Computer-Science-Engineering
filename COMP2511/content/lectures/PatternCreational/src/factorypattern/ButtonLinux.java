package factorypattern;

public class ButtonLinux implements Button {

	private String labelText = "";
	@Override
	public void setLabel(String labelText) {
		this.labelText = labelText;
		System.out.println("ButtonLinux: Setting label " + labelText);
		
	}

	@Override
	public void click() {
		
		System.out.println("ButtonLinux: clicking button with label " + this.labelText);
		
	}

	
	
}
