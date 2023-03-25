package example;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.SortedMap;

public abstract class MyReportTemplate {
	
	
	public void genReport() {
		
		InputStream f1 = openFile();
		
		SortedMap<String, ArrayList<String>> data = parseFile( f1 );
		
		generateReport ( data );
		
		if( isRequestedSummary()) {
			generateSummary(data);
		}
		
		
	}

	public void generateSummary(SortedMap<String, ArrayList<String>> data) {
		System.out.println("generating Summary (default from MyReportTemplat ...");

	}

	public boolean isRequestedSummary() {
		
		return false;
	}

	public void generateReport(SortedMap<String, ArrayList<String>> data) {
		System.out.println("generating report (default from MyReportTemplat ...");
		
	}

	protected abstract SortedMap<String, ArrayList<String>> parseFile(InputStream f1);

	public InputStream openFile() {
	
		String filename = getFilename();
		InputStream f1 = null;
		
		try {
			f1 = new FileInputStream(filename);
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		}
		
		return f1;
	}

	public abstract String getFilename(); 
	

}
