package example;

public class Customer implements Comparable<Customer>{
	
	String name;
	int rewardsPoints;
	int postcode;
	
	public Customer(String name, int rewardsPoints, int postcode) {
		super();
		this.name = name;
		this.rewardsPoints = rewardsPoints;
		this.postcode = postcode;
	}
	public String getName() {
		return name;
	}
	public void setName(String name) {
		this.name = name;
	}
	public int getRewardsPoints() {
		return rewardsPoints;
	}
	public void setRewardsPoints(int rewardsPoints) {
		this.rewardsPoints = rewardsPoints;
	}
	public int getPostcode() {
		return postcode;
	}
	public void setPostcode(int postcode) {
		this.postcode = postcode;
	}
	@Override
	public String toString() {
		
		String s1 = "[" + getName() + "," + getRewardsPoints() + "," + getPostcode() + "]";
		
		return s1;
	}
	
	
	@Override
	public int compareTo(Customer other) {

		/*
		 * if( this.getPostcode() < other.getPostcode()) { return -1; } else if (
		 * this.getPostcode() == other.getPostcode()) { return 0; } else { return 1; }
		 */
	
		//return this.getPostcode() - other.getPostcode() ;
		
		return this.getName().compareTo(other.getName()); 
	}	

}
