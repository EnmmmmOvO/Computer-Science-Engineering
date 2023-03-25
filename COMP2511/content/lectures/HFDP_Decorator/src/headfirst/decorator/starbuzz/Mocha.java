package headfirst.decorator.starbuzz;

public class Mocha extends CondimentDecorator {
	Beverage beverage;
 
	public Mocha(Beverage beverage) {
		this.beverage = beverage;
	}
 
	public String getDescription() {
		return beverage.getDescription() + ", Mocha";
	}
 
	public double cost() {
		double beverage_cost = beverage.cost();
		 
		System.out.println("Mocha: beverage.cost() is: " + beverage_cost );		
		System.out.println("  - adding One Mocha cost of 0.20c ");
		System.out.println("  - new cost is: " + (0.20 + beverage_cost ) );
		
		return 0.20 + beverage_cost ;
	}
}
