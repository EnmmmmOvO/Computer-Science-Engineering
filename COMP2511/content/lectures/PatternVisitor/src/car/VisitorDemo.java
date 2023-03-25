package car;

public  class VisitorDemo {
	
    public static void main(final String[] args) {
    	
        Car car = new Car();

        System.out.println("\n ------ From CarElementPrintVisitor -------- -------- -------- ");
        car.accept(new CarElementPrintVisitor());
        
        System.out.println("\n ------ From CarElementDoVisitor -------- -------- -------- ");
        CarElementDoVisitor carVisitorDo = new CarElementDoVisitor(); 
        
        car.accept(carVisitorDo);
        
        
        System.out.println("Total Cost is: " + carVisitorDo.getTotalCost());
    }
    
}