/** 
 * Aarthi N
 */
package solution1;
/*
 * Refactoring Technique 1: Extract Method
 * In this refactoring, the switch block inside the statement() method has been extracted to a new method
 * calculateRental().  This refactoring has helped to encapsulate the calculation of the rental charge 
 * to a method, and this method can be reused by different methods, e.g, if we wanted to print a HTML statement 
 */

import java.util.ArrayList;
import java.util.List;

public class Customer {
	
	private String _name;
	private List<Rental> _rentals = new ArrayList<>();
	public Customer (String name) {
		_name = name;
	};
	
	public void addRental(Rental rental) {
		_rentals.add(rental);
	}
	
	public String getName (){
		return _name;
	}
	
	public String statement() {
		
		double totalAmount = 0;
		String result = "Rental Record for " + getName() + "\n";
		
		for (Rental r: _rentals) {
			double thisAmount = 0;
			// Refactoring technique 1: Extract Method
			// Here, priceCode is not modified, thisAmount is modified. any non-modified code
			// can be passed as a parameter and a modified variable can be returned as the result
			thisAmount = calcRentalAmount(r);
			//show figures for this rental
			result += "\t" + r.getMovie().getTitle() + "\t" + 	String.valueOf(thisAmount) + "\n";
			totalAmount += thisAmount;
			
		}

		//add footer lines
		result += "Amount owed is " + String.valueOf(totalAmount) +	"\n";
		return result;
	}
	
	double calcRentalAmount(Rental r) {
		double thisAmount = 0;
		int priceCode = r.getMovie().getPriceCode();
		switch (priceCode) {
			case Movie.REGULAR:
				thisAmount += 2;
				if (r.getDaysRented() > 2)
					thisAmount += (r.getDaysRented() - 2) * 1.5;
			break;
			case Movie.NEW_RELEASE:
				thisAmount += r.getDaysRented() * 3;
			break;
			case Movie.CHILDRENS:
				thisAmount += 1.5;
				if (r.getDaysRented() > 3)
					thisAmount += (r.getDaysRented() - 3) * 1.5;
			break;
		}
		return thisAmount;
	}
}
