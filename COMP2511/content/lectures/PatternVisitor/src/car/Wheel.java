package car;

public class Wheel implements CarElementVisitable {

	private final String name;
	private double cost = 210;

	public Wheel(final String name) {
		this.name = name;
	}

	public String getName() {
		return name;
	}

	@Override
	public void accept(CarElementVisitor visitor) {
		/*
		 * accept(CarElementVisitor) in Wheel implements accept(CarElementVisitor) in
		 * CarElement, so the call to accept is bound at run time. This can be
		 * considered the *first* dispatch. However, the decision to call visit(Wheel)
		 * (as opposed to visit(Engine) etc.) can be made during compile time since
		 * 'this' is known at compile time to be a Wheel. Moreover, each implementation
		 * of CarElementVisitor implements the visit(Wheel), which is another decision
		 * that is made at run time. This can be considered the *second* dispatch.
		 */
		visitor.visit(this);
	}

	public double getCost() {
		return cost;
	}

	public void setCost(double cost) {
		this.cost = cost;
	}

}
