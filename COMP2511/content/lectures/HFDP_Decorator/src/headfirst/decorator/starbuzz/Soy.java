package headfirst.decorator.starbuzz;

public class Soy extends CondimentDecorator {
	Beverage beverage;

	public Soy(Beverage beverage) {
		this.beverage = beverage;
	}

	public String getDescription() {
		return beverage.getDescription() + ", Soy";
	}

	public double cost() {
		double beverage_cost = beverage.cost(); 
		System.out.println("Soy: beverage.cost() is: " + beverage_cost);		
		System.out.println("  - adding One Soy cost of 0.15c ");
		System.out.println("  - new cost is: " + (0.15 + beverage_cost ) );
		
		return 0.15 + beverage.cost();
	}
}
