package example;

import java.util.SortedMap;
import java.util.ArrayList;

public class CSVReportWithSummary extends CSVReport {

	@Override
	public boolean isRequestedSummary() {
		
		return true;
	}

	@Override
	public void generateReport(SortedMap<String, ArrayList<String>> data) {
		System.out.println("generating report (from CSVReportWithSummary ...");
		
	}
	

}
