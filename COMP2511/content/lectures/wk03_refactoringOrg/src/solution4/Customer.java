package solution4;
/*
 * Applying the Replace Temp with Query refactoring technique to get rid of the local variable totalAmount.
 * This refactoring is questionable, as performing this refactoring has resulted in an increase in performance
 * due to the for loop now being performed twice.
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
		
		String result = "Rental Record for " + getName() + "\n";
		
		for (Rental r: _rentals) {
			//show figures for this rental
			result += "\t" + r.getMovie().getTitle() + "\t" + 	String.valueOf(r.getCharge()) + "\n";
		}

		//add footer lines
		result += "Amount owed is " + String.valueOf(getTotalCharge()) +	"\n";
		return result;
	}

// Two options: Sometimes leave the old method to delegate to the old method.  This is useful if it is a public
// method 
	
	private double getCharge(Rental r) {
		return r.getCharge();
	}
	
	private double getTotalCharge() {
		double result = 0;
		for (Rental r: _rentals) {
			result += r.getCharge();
		}
		return result;
	}
}
