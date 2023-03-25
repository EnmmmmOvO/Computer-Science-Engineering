package car;

public class BodyPart2 implements CarElementVisitable {
	
	private double cost = 3200;

	@Override
	public void accept(CarElementVisitor visitor) {
		visitor.visit(this);
	}

	public double getCost() {
		return cost;
	}

	public void setCost(double cost) {
		this.cost = cost;
	}

}
