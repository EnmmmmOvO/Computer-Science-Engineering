package factorypattern;

public class GUIFactoryLinux implements GUIFactory {

	@Override
	public Button getButton() {
		return new ButtonLinux();
	}

	@Override
	public CheckBox getCheckBox() {
		return new CheckBoxLinux();
	}
	
}
