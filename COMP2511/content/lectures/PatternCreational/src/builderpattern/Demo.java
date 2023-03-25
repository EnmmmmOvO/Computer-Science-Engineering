package builderpattern;

/**
 * Demo class. Everything comes together here.
 */
public class Demo {

    public static void main(String[] args) {
    	
        System.out.println("\n ------- Car Built Below (without Director) -----------");
    	
    	AbcCarBuilder builder1 = new AbcCarBuilder();
    	
    	builder1.setType(Type.SPORTS_CAR);
    	builder1.setSeats(2);
    	builder1.setEngine(new Engine(3.0, 0));
    	builder1.setTransmission(Transmission.SEMI_AUTOMATIC);
    	builder1.setTripComputer(new TripComputer());
    	builder1.setGPSNavigator(new GPSNavigator());
    	
    	Car car1 = builder1.getResult();
        System.out.println("\n" + car1);       
        
        System.out.println("\n ------- Car Built Below (using Director) ----------- ");
            	
        CarDirector director = new CarDirector();
        
        // Director gets the concrete builder object from the client
        // (application code). That's because application knows better which
        // builder to use to get a specific product.
        AbcCarBuilder builder = new AbcCarBuilder();
        director.constructCityCar(builder);

        // The final product is often retrieved from a builder object, since
        // Director is not aware and not dependent on concrete builders and
        // products.
        Car car = builder.getResult();
        System.out.println("\n" + car);
        
        
        System.out.println("\n ------- Car Manual Below (using Director) -----------");

        AbcCarManualBuilder manualBuilder = new AbcCarManualBuilder();

        // Director may know several building recipes.
        director.constructCityCar(manualBuilder);
        Manual carManual = manualBuilder.getResult();
        System.out.println( "\n" + carManual.print() );
    }

}
