package car;

import java.util.ArrayList;

public class Body implements CarElementVisitable {

	private ArrayList<CarElementVisitable> elements = new ArrayList<CarElementVisitable>();

	private double cost = 2000;

	public Body() {
		this.elements.add(new BodyPart1());
		this.elements.add(new BodyPart2());
	}

	@Override
	public void accept(CarElementVisitor visitor) {

		for (CarElementVisitable element : elements) {
			element.accept(visitor);
		}

		visitor.visitBody(this);
	}

	public double getCost() {
		return cost;
	}

	public void setCost(double cost) {
		this.cost = cost;
	}
}
