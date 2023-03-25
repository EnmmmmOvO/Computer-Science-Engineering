package ShoppingCart;

import java.util.ArrayList;

public class MyCart {

	private Customer cust;
	private ArrayList<Item> items = new ArrayList<Item>() ; 

	
	public MyCart(Customer cust) {
		super();
		this.cust = cust;
	}

	
	public void add(Item it) {
		items.add(it);
	}
	
	
	public Customer getCust() {
		return cust;
	}
	
	public void setCust(Customer cust) {
		this.cust = cust;
	}

	public ArrayList<Item> getItems() {
		return items;
	}

	public void setItems(ArrayList<Item> items) {
		this.items = items;
	}

	public static void main(String[] args) {
		// TODO Auto-generated method stub

	}


	public void printItems() {
		// TODO Auto-generated method stub
		for( Item it : items) {
			System.out.println(it);
			
		}
		
		
	}

}
