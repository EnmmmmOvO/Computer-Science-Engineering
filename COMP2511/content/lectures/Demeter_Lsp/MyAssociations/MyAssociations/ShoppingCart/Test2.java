package ShoppingCart;

public class Test2 {

	public static void main(String[] args) {		
		
		Customer customer1 = new Customer("23145", "John Smith", "100 George St, Sydney");
		MyCart cart1 = new MyCart(customer1); 
		
		cart1.add( new Item("aaaa", 2));
		cart1.add(new Item("bbb", 5));
		cart1.add(new Item("ccc", 8));
		
	
		cart1.printItems();
		
		cart1 = null;
		
		System.out.println(customer1.getName());
		
		
		

	}

}
