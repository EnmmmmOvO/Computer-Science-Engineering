package car;

public interface CarElementVisitor {

    void visitBody(Body body);
	void visit(BodyPart1 bodyPart1);
	void visit(BodyPart2 bodyPart2);
	    
	void visit(Wheels wheels);
    void visit(Wheel wheel);
    
    void visit(Car car);
    void visit(Engine engine);
    
}
