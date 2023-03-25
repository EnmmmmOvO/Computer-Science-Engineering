package car;

public class Engine implements CarElementVisitable {

	private double cost = 4000;

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
