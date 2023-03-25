package car;

import java.util.ArrayList;

public class Car implements CarElementVisitable {
	
    private ArrayList<CarElementVisitable> elements = 
    		new ArrayList<CarElementVisitable>();
    
	private double cost = 6000;

    public Car() {        
        this.elements.add( new Wheels() );
        this.elements.add( new Body() );
        this.elements.add( new Engine() );  
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