/** 
 * Aarthi N
 */
package original;

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
	
	/* Discuss problems with this method */
	public String statement() {
		
		double totalAmount = 0;
		String result = "Rental Record for " + getName() + "\n";
		
		for (Rental r: _rentals) {
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
			
			//show figures for this rental
			result += "\t" + r.getMovie().getTitle() + "\t" + 	String.valueOf(thisAmount) + "\n";
			totalAmount += thisAmount;
			
		}

		//add footer lines
		result += "Amount owed is " + String.valueOf(totalAmount) +	"\n";
		return result;
	}
	
	public static void main(String[] args) {
		Customer c1 = new Customer("Mary Jane Watson");
		Movie  m = new Movie("Gone with the wind",Movie.REGULAR);
		Rental r = new Rental(m, 3);
		c1.addRental(r);
		
		m = new Movie("Finding Nemo",Movie.CHILDRENS);
		r = new Rental(m, 7);
		c1.addRental(r);
		
		System.out.println(c1.statement());
		
	}
}
