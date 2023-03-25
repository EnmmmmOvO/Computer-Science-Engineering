package headfirst.strategy;

public class MiniDuckSimulator {
 
	public static void main(String[] args) {
 
		MallardDuck	mallard = new MallardDuck();
		RubberDuck	rubberDuckie = new RubberDuck();
		DecoyDuck	decoy = new DecoyDuck();
 
		ModelDuck	model = new ModelDuck();

		System.out.println(" ====== 1 ======== ");
		mallard.performQuack();
		rubberDuckie.performQuack();
		decoy.performQuack();

		System.out.println(" ====== 2 ======== ");
		model.performFly();	
		model.setFlyBehavior(new FlyRocketPowered());
		model.performFly();
		System.out.println(" ============== ");

	}
}
