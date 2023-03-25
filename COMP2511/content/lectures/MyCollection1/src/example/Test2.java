package example;

import java.util.ArrayList;
//import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.TreeSet;

public class Test2 {

	public static void main(String[] args) {
		
		Comparator<Customer> myCmp  = new Comparator<Customer>() {
			
			@Override
			public int compare(Customer o1, Customer o2) {
				
				if(o1.getPostcode() != o2.getPostcode()) {
					return o1.getPostcode() -  o2.getPostcode() ; 
				}
				
				// now postcodes are same .. 
				return o1.getRewardsPoints() -  o2.getRewardsPoints() ; 
				
			}
		} ; 
		
		
		TreeSet<Customer> set = new TreeSet<>();
		set.add(new Customer("John", 12500, 2060));
		set.add(new Customer("Emma", 45900, 2200));
		set.add(new Customer("Peter", 700, 2060));
		set.add(new Customer("Kylie", 110200, 2075));

		ArrayList<Customer> custA = new ArrayList<Customer>(set);

		for (Customer c : custA) {
			System.out.println(c);
		}
		
		custA.sort( myCmp );
		System.out.println(" ======================== ");
		for (Customer c : custA) {
			System.out.println(c);
		}
		
		
		Collections.sort( custA , myCmp);
		
		
		
		

	}

}
