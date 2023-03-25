package car;

public class CarElementDoVisitor implements CarElementVisitor {
	private double totalCost = 0;

	@Override
	public void visitBody(Body body) {
		System.out.println("Moving my body");
		totalCost += body.getCost();
		System.out.println(" - cost added: " + body.getCost()); 		
	}

	@Override
	public void visit(Car car) {
		System.out.println("Starting my car");
		totalCost += car.getCost();
		System.out.println(" - cost added: " + car.getCost()); 
	}

	@Override
	public void visit(Wheel wheel) {
		System.out.println("Kicking my " + wheel.getName() + " wheel");
		totalCost += wheel.getCost();
		System.out.println(" - cost added: " + wheel.getCost()); 				
	}

	@Override
	public void visit(Engine engine) {
		System.out.println("Starting my engine");
		totalCost += engine.getCost();
		System.out.println(" - cost added: " + engine.getCost()); 				
	}

	@Override
	public void visit(BodyPart1 bodyPart1) {
		System.out.println("Adding my bodyPart1");
		totalCost += bodyPart1.getCost();
		System.out.println(" - cost added: " + bodyPart1.getCost()); 				
	}

	@Override
	public void visit(BodyPart2 bodyPart2) {
		System.out.println("Adding my bodyPart2");
		totalCost += bodyPart2.getCost();
		System.out.println(" - cost added: " + bodyPart2.getCost()); 

	}

	@Override
	public void visit(Wheels wheels) {
		System.out.println("Adding my wheels");
		totalCost += wheels.getCost();
		System.out.println("  - cost added: " + wheels.getCost()); 		
	}

	public double getTotalCost() {
		return totalCost;
	}

}
