package example;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.TreeSet;

public class ComparatorSimple {

	public static void main(String[] args) {
		
		Comparator<Customer> myCmp  = new MyPostcodeRewardspointCmp()  ; 
		
		
		TreeSet<Customer> set = new TreeSet<>();
		set.add(new Customer("John", 12500, 2060));
		set.add(new Customer("Emma", 45900, 2200));
		set.add(new Customer("Peter", 700, 2061));
		set.add(new Customer("Kylie", 110200, 2075));

		ArrayList<Customer> custA = new ArrayList<Customer>(set);

		for (Customer c : custA) {
			System.out.println(c);
		}

		Collections.sort( custA );
		System.out.println(" =========  1  =============== ");
		for (Customer c : custA) {
			System.out.println(c);
		}

		Collections.sort( custA , myCmp);
		
		System.out.println(" =========== 2 ============= ");
		for (Customer c : custA) {
			System.out.println(c);
		}
		
		Collections.sort( custA , myCmp);
		
	

	}

}
