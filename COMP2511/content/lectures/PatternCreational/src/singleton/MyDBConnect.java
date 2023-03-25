package singleton;

import java.io.File;

public class MyDBConnect {

	private static File  myLogFile = null;

	private MyDBConnect() {

    }

	public static synchronized File getFileCon() {

		if (myLogFile == null) {
			myLogFile = new File("LogFile.txt");
		}
		return myLogFile;
	}


}
