/**
 * Demo file, it may not be correct and/or complete.  
 * Please watch the corresponding lecture(s) for more explanations.
 * 
 * @author ashesh
 */


package ShoppingCart;

public class Item {

	private String itemId;
	private int quantity;
	
	public Item(String itemId, int quantity) {
		super();
		this.itemId = itemId;
		this.quantity = quantity;
	}

	public String getItemId() {
		return itemId;
	}

	
	public int getQuantity() {
		return quantity;
	}

	public void setQuantity(int quantity) {
		this.quantity = quantity;
	}

	@Override
	public String toString() {
 		String str = getItemId() + " : " + getQuantity() ;			
		return str;
	}

	
	
}
