package factorypattern;

public class CheckBoxLinux implements CheckBox {

	private String text = "";
	private boolean status = false;
	
	@Override
	public void setText(String text) {
		this.text = text;
		System.out.println("CheckBoxLinux: Setting Text " + this.text);

	}

	@Override
	public String getText() {
		return this.text;
	}	
	
	@Override
	public void setStatus(boolean status) {
		this.status = status;
		System.out.println("CheckBoxLinux: setStatus status " + this.status);

	}

	@Override
	public boolean getStatus() {
		return this.status;
	}



}
