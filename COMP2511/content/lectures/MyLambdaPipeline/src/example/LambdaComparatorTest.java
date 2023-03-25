package example;

import java.util.ArrayList;
//import java.util.Collection;
import java.util.Comparator;
import java.util.TreeSet;

public class LambdaComparatorTest {

	public static void main(String[] args) {
				
		TreeSet<Customer> set = new TreeSet<>();
		set.add(new Customer("John", 12500, 2060));
		set.add(new Customer("Emma", 45900, 2200));
		set.add(new Customer("Peter", 700, 2060));
		set.add(new Customer("Kylie", 110200, 2075));

		ArrayList<Customer> custA = new ArrayList<Customer>(set);
		//Traditional print - using a for loop
		for (Customer c : custA) {
			System.out.println(c);
		}
		
		//Using an anonymous inner class
		Comparator<Customer> myCmpAnonymous  = new Comparator<Customer>() {
			@Override
			public int compare(Customer o1, Customer o2) {
				return o1.getRewardsPoints() -  o2.getRewardsPoints() ; 
			}
		} ; 
		custA.sort( myCmpAnonymous );


		//Using Lambda expression - simple example (only one line)
		custA.sort((Customer o1, Customer o2)->o1.getRewardsPoints() - o2.getRewardsPoints());
	
		//Print using Lambda expression
		System.out.println("\n ------- Using Lambda Expression ------- ");
		custA.forEach( (cust) -> System.out.println(cust) );
		
		//Using Lambda expression - Another example (with return)
		custA.sort( (Customer o1, Customer o2)-> {
			if(o1.getPostcode() != o2.getPostcode()) {
				return o1.getPostcode() -  o2.getPostcode() ; }
			return o1.getRewardsPoints() -  o2.getRewardsPoints() ; 
		});

		System.out.println(" ------- Another example using Lambda ------- ");
		custA.forEach( (cust) -> System.out.println(cust) );

	}

}
