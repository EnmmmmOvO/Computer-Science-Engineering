public class Stock {
	
    private String name = "";
    private int quantity = 0;
 
    public Stock(String name, int qty){
        this.name = name;
        this.quantity = qty;
    }

    public void buy(){
       System.out.println("Stock [ Name: "+name+
       ", Quantity: " + quantity +" ] bought");
    }
    public void sell(){
       System.out.println("Stock [ Name: "+name+
       ", Quantity: " + quantity +" ] sold");
    }    
}
