package factorymethod;

public class Test1 {

	public static void main(String[] args) {

		
		Button b1 = ButtonFactory.getButton();
		b1.setLabel("Label 1");
		
		Button b2 = ButtonFactory.getButton("html");
		b2.setLabel("Label 2");

		System.out.println("-------- ---------- ");		
		System.out.println(b1);
		System.out.println("-------- ---------- ");		
		System.out.println(b2);
		
		
		/**
		 * Alternative ... instance Method ... 
		 */
		System.out.println("\n\n***** Using Instance Method ***** \n");		

				
		ButtonFactory2 btnFactory =  new ButtonFactory2();
		
		Button b3 = btnFactory.generateButton();
		b3.setLabel("Button 3");
		
		Button b4 = btnFactory.generateButton();
		b4.setLabel("Button 4");		
		
		ButtonFactory2 btnFactoryHtml =  new ButtonFactory2("html");
		
		Button b5 = btnFactoryHtml.generateButton();
		b5.setLabel("Button 5");

		Button b6 = btnFactoryHtml.generateButton();
		b6.setLabel("Button 6");
		
		System.out.println("-------- ---------- ");		
		System.out.println(b3);
		System.out.println("-------- ---------- ");		
		System.out.println(b4);
		System.out.println("-------- ---------- ");		
		System.out.println(b5);
		System.out.println("-------- ---------- ");		
		System.out.println(b6);		


		
	}

}
