package car;

public class BodyPart1 implements CarElementVisitable {

	private double cost = 2500;

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
