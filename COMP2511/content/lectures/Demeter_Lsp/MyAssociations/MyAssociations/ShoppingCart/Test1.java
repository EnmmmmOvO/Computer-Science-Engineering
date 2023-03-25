/**
 * Demo file, it may not be correct and/or complete.  
 * Please watch the corresponding lecture(s) for more explanations.
 * 
 * @author ashesh
 */

package ShoppingCart;

public class Test1 {

	public static void main(String[] args) {
		// TODO Auto-generated method stub

		
		Customer customer1 = new Customer("5123", "John Smith", "10000, George Street, Sydney, NSW 2000");
		
		Cart cart1 = new Cart(customer1);
		
		cart1.addItem( new Item("4123", 4));
		cart1.addItem( new Item("7721", 1));
		cart1.addItem( new Item("8251", 2));
		cart1.addItem( new Item("3751", 6));

		cart1.printCart();
		//  .. more here 
		// ...... 
		
		// we don't need cart1 anymore , discarding cart1.
		cart1 = null; 
		// items list for cart1 is also destroyed.
		// However, cust1 still remain. 
		
		System.out.println(customer1.getName());

	}

}
