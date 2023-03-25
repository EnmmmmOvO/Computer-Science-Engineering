public class CommandPatternDemo {
    
    public static void main(String[] args) {
        Stock rioStock = new Stock("RIO", 25);
        Stock bhpStock = new Stock("BHP", 12);

        BuyStock buyStockOrder = new BuyStock(rioStock);
        SellStock sellBHPStockOrder = new SellStock(bhpStock);
        SellStock sellCBAStockOrder = new SellStock(new Stock("CBA", 43));

        
        Broker broker = new Broker();
        broker.takeOrder(buyStockOrder);
        broker.takeOrder(sellBHPStockOrder);
        broker.takeOrder(sellCBAStockOrder);
  
        broker.placeOrders();
     }    
}
