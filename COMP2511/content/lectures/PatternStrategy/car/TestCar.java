package car;

public class TestCar {

	public static void main(String[] args) {
		
		Car c1 = new Car(new EngineNormal(), new Brake123());
		c1.brakeApply();
		c1.engineRun();
		System.out.println("--------------- ");

		Car c2 = new Car(new EngineTurbo(), new BrakeABS());
		c2.brakeApply();
		c2.engineRun();
		System.out.println("--------------- ");
		
		Car c3 = new ToyotaCamryHybrid543();
		c3.brakeApply();
		c3.engineRun();
		System.out.println("--------------- ");		
		
	}

}
