package factorypattern;

public class Test1 {

	public static void generateButtonCheckBox(GUIFactory guiFactory) {
		
		Button b1 = guiFactory.getButton();
		b1.setLabel("Hello!");
		b1.click();
		
		CheckBox ch1 = guiFactory.getCheckBox();
		ch1.setText("Select this if you prefer XYZ ");
		ch1.setStatus(true);
	
		System.out.println(ch1.getStatus());				
	}
	
	public static void main(String[] args) {
		
		GUIFactory factory = new GUIFactoryWin();
		generateButtonCheckBox( factory );

		System.out.println(" -------------- ------------ ----------  ");
		
		factory = new GUIFactoryLinux();
		generateButtonCheckBox( factory );
	
		return;
	}

}
