package factorypattern;

public class GUIFactoryWin implements GUIFactory {

	@Override
	public Button getButton() {
		return new ButtonWin();
	}

	@Override
	public CheckBox getCheckBox() {
		return new CheckBoxWin();
	}
	
}
