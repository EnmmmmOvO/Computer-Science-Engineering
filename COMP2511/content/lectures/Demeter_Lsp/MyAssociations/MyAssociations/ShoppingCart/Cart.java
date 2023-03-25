/**
 * Demo file, it may not be correct and/or complete.  
 * Please watch the corresponding lecture(s) for more explanations.
 * 
 * @author ashesh
 */

package ShoppingCart;

import java.util.ArrayList;

public class Cart {

	//has-a relationship (aggregation) 
	Customer customer;
	
	//composition - death relationship!
	ArrayList<Item> items = new ArrayList<Item>();
	
	public Cart(Customer customer) {
		super();
		this.customer = customer;
	}
	
	public void addItem(Item item) {
		items.add(item);
	}
	
	public void printCart() {
		
		
		for(int i=0; i < items.size(); i++) {
			System.out.println(items.get(i));			
		}
		
		
		/**   Alternatively ... 
		 
		for(Item it : this.items) {
			System.out.println(it);			
		}
		
		 */
			
		
	}
	
}
