package example;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.SortedMap;
import java.util.TreeMap;


public class CSVReport extends MyReportTemplate{
	private String fname = "";
	private boolean reqSummary = false;
	
	public CSVReport() {
		super();
		fname = "src/example/data.csv";
		reqSummary = false;
	}
	public CSVReport(String filename, boolean requestSummary) {
		this.fname = filename;
		this.reqSummary = requestSummary;
	}

	@Override
	protected SortedMap<String, ArrayList<String>> parseFile(InputStream f1) {
		// CSV parsing code here 
		System.out.println("parsing CSV data file: " + getFilename());
		TreeMap<String, ArrayList<String>> data = new TreeMap<String, ArrayList<String>>();
		// populate data object in this method  .. 
		
		return data;
	}

	@Override
	public String getFilename() {
		// ask user for a file name.. 
		return fname;
	}

	@Override
	public boolean isRequestedSummary() {
		
		return this.reqSummary;
	}

	
	
	
}
