package solution4;

public class Rental {
	private Movie _movie;
	private int _daysRented;
	
	public Rental(Movie movie, int daysRented) {
		_movie = movie;
		_daysRented = daysRented;
	}
	
	public int getDaysRented() {
		return _daysRented;
	}
	
	public Movie getMovie() {
		return _movie;
	}

	double getCharge() {
		double thisAmount = 0;
		int priceCode = getMovie().getPriceCode();
		switch (priceCode) {
			// Class rental is tightly coupled with class Movie - switch statement based on the data of another object
			// is a bad idea
			// getCharge() must be moved to class Movie
			case Movie.REGULAR:
				thisAmount += 2;
				if (getDaysRented() > 2)
					thisAmount += (getDaysRented() - 2) * 1.5;
			break;
			case Movie.NEW_RELEASE:
				thisAmount += getDaysRented() * 3;
			break;
			case Movie.CHILDRENS:
				thisAmount += 1.5;
				if (getDaysRented() > 3)
					thisAmount += (getDaysRented() - 3) * 1.5;
			break;
		}
		return thisAmount;
	}

	int getFrequentRenterPoints() {
		if (_movie.getPriceCode() == Movie.NEW_RELEASE && (_daysRented > 1)) 
			return 2;
		else 
			return 1;	
	}


}
