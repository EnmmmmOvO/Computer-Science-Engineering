package car;

public class CarElementPrintVisitor implements CarElementVisitor {

	   @Override
	    public void visitBody(Body body) {
	        System.out.println("Visiting body");
	    }

	    @Override
	    public void visit(Car car) {
	        System.out.println("Visiting car");
	    }

	    @Override
	    public void visit(Engine engine) {
	        System.out.println("Visiting engine");
	    }

	    @Override
	    public void visit(Wheel wheel) {
	        System.out.println("Visiting " + wheel.getName() + " wheel");
	    }

		@Override
		public void visit(BodyPart1 bodyPart1) {
	        System.out.println("Visiting bodyPart1");
			
		}

		@Override
		public void visit(BodyPart2 bodyPart2) {
	        System.out.println("Visiting bodyPart2");
			
		}

		@Override
		public void visit(Wheels wheels) {
	        System.out.println("Visiting wheels");
			
		}
	
	
	
}
