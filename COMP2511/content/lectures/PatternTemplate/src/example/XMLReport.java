package example;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.SortedMap;
import java.util.TreeMap;

public class XMLReport extends MyReportTemplate {
	
	private String fname = "";
	public XMLReport(String filename) {
		fname = filename;
	}

	@Override
	protected SortedMap<String, ArrayList<String>> parseFile(InputStream f1) {
		System.out.println("parsing XML  data file: " + getFilename());
		TreeMap<String, ArrayList<String>> data = new TreeMap<String, ArrayList<String>>();
		// populate data object in this method  .. 
		return data;
	}

	@Override
	public String getFilename() {
		return fname;
	}
	

}
