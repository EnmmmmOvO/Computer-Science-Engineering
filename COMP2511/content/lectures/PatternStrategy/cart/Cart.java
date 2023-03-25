package cart;
/** Demo file, it may not be correct and/or complete.  
 * Please watch the corresponding lecture(s) for more explanations.
 * @author ashesh
 */

import java.util.ArrayList;

public class Cart {

	ArrayList<Item> list;
	
	PaymentOption payment ;
	ShippingOption shipping;
	
	/**
	 * other fields  here
	 */
	
	
	public Cart() {
		payment = new CardPayment();
		shipping = new ShippingAirTransport();
	}

	public Cart(PaymentOption payment, ShippingOption shipping) {
		this.payment = payment;
		this.shipping = shipping;
	}

	
	/**
	 * Method forwarding using the current shipping option
	 * @return
	 */
	public double calShippingCharges() {
		
		return shipping.calculateCharges(list);
		
	}

	
	/**
	 * Method forwarding using the current payment option
	 * @return
	 */
	public boolean chargeAmount(double amt) {
		
		return payment.charge(amt);
	}
	
	/**
	 * Getters/Setters
	 */
	public PaymentOption getPayment() {
		return payment;
	}

	public void setPayment(PaymentOption payment) {
		this.payment = payment;
	}

	public ShippingOption getShipping() {
		return shipping;
	}

	public void setShipping(ShippingOption shipping) {
		
		this.shipping = shipping;
	}
	
	/**
	 * other methods here
	 */
	
}
