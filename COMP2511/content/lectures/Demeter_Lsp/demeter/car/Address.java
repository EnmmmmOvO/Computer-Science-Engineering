/**
 * Demo file, it may not be correct and/or complete.  
 * Please watch the corresponding lecture(s) for more explanations.
 * 
 * @author ashesh
 */

package car;

public class Address {

	private String houseNo ;
	private String street;
	private String suburb;
	private String state;
	private String country;
	private String postcode;
	
	public Address(String houseNo, String street, String suburb, String state, String country, String postcode) {
		super();
		this.houseNo = houseNo;
		this.street = street;
		this.suburb = suburb;
		this.state = state;
		this.country = country;
		this.postcode = postcode;
	}
	
	public String getHouseNo() {
		return houseNo;
	}
	public void setHouseNo(String houseNo) {
		this.houseNo = houseNo;
	}
	public String getStreet() {
		return street;
	}
	public void setStreet(String street) {
		this.street = street;
	}
	public String getSuburb() {
		return suburb;
	}
	public void setSuburb(String suburb) {
		this.suburb = suburb;
	}
	public String getState() {
		return state;
	}
	public void setState(String state) {
		this.state = state;
	}
	public String getCountry() {
		return country;
	}
	public void setCountry(String country) {
		this.country = country;
	}
	public String getPostcode2() {
		return postcode;
	}
	public void setPostcode(String postcode) {
		this.postcode = postcode;
	}
	
	
}
