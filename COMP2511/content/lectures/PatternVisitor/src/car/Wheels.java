package car;

import java.util.ArrayList;

public class Wheels implements CarElementVisitable {

	private ArrayList<CarElementVisitable> elements = new ArrayList<CarElementVisitable>();
	private double cost = 0;
	
	public Wheels() {
		this.elements.add(new Wheel("front left"));
		this.elements.add(new Wheel("front right"));
		this.elements.add(new Wheel("back left"));
		this.elements.add(new Wheel("back right"));
	}

	@Override
	public void accept(CarElementVisitor visitor) {

		for (CarElementVisitable element : elements) {
			element.accept(visitor);
		}

		visitor.visit(this);
	}

	public double getCost() {
		return cost;
	}

	public void setCost(double cost) {
		this.cost = cost;
	}
}
