package example;

import java.util.Comparator;

public class MyPostcodeRewardspointCmp implements Comparator<Customer>{

	@Override
	public int compare(Customer o1, Customer o2) {
		
		if(o1.getPostcode() != o2.getPostcode()) {
			return o1.getPostcode() -  o2.getPostcode() ; 
		}
		
		// now postcodes are same .. 
		return o1.getRewardsPoints() -  o2.getRewardsPoints() ; 
		
	}
	
	

}
