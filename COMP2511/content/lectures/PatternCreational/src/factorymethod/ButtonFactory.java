package factorymethod;

public class ButtonFactory {

	public static Button getButton() {
		
		String platform = System.getProperty("os.name");

		return getButton(platform);
	}

	public static Button getButton(String platform) {
		Button btn = null;

		if (platform.equalsIgnoreCase("Html")) {
			btn = new ButtonHtml();
		} else if (platform.equalsIgnoreCase("Windows 10")) {  // this may be different! 
			btn = new ButtonWin10();
		} else if (platform.equalsIgnoreCase("MacOs")) {  // this may be different! 
			btn = new ButtonMacOs();
		} else if (platform.equalsIgnoreCase("Linux")) {
			btn = new ButtonLinux();
		} else {
			new Exception("Unknwon platform type!");
		}

		return btn;
	}

}
