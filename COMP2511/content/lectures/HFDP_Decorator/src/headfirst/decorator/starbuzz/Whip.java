package headfirst.decorator.starbuzz;
 
public class Whip extends CondimentDecorator {
	Beverage beverage;
 
	public Whip(Beverage beverage) {
		this.beverage = beverage;
	}
 
	public String getDescription() {
		return beverage.getDescription() + ", Whip";
	}
 
	public double cost() {
		double beverage_cost = beverage.cost(); 
		System.out.println("Whipe: beverage.cost() is: " + beverage_cost);		
		System.out.println("  - adding One Whip cost of 0.10c ");
		System.out.println("  - new cost is: " + (0.10 + beverage_cost ) );
		
		return 0.10 + beverage_cost ;
	}
}
