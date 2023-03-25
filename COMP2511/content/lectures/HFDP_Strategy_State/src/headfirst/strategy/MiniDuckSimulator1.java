package headfirst.strategy;

public class MiniDuckSimulator1 {
 
	public static void main(String[] args) {
 
		System.out.println(" ============== ");
		Duck mallard = new MallardDuck();
		mallard.performQuack();
		mallard.performFly();
   
		System.out.println(" ============== ");
		Duck model = new ModelDuck();
		model.performFly();
		model.setFlyBehavior(new FlyRocketPowered());
		model.performFly();
		System.out.println(" ============== ");

	}
}
