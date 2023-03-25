package builderpattern;

/**
 * Car is a product class.
 */
public class Car {
    private final Type type;
    private final int seats;
    private final Engine engine;
    private final Transmission transmission;
    private final TripComputer tripComputer;
    private final GPSNavigator gpsNavigator;
    private double fuel = 0;

    public Car(Type type, int seats, Engine engine, Transmission transmission,
               TripComputer tripComputer, GPSNavigator gpsNavigator) {
        this.type = type;
        this.seats = seats;
        this.engine = engine;
        this.transmission = transmission;
        this.tripComputer = tripComputer;
        this.tripComputer.setCar(this);
        this.gpsNavigator = gpsNavigator;
    }

    public Type getType() {
        return type;
    }

    public double getFuel() {
        return fuel;
    }

    public void setFuel(double fuel) {
        this.fuel = fuel;
    }

    public int getSeats() {
        return seats;
    }

    public Engine getEngine() {
        return engine;
    }

    public Transmission getTransmission() {
        return transmission;
    }

    public TripComputer getTripComputer() {
        return tripComputer;
    }

    public GPSNavigator getGpsNavigator() {
        return gpsNavigator;
    }

	@Override
	public String toString() {
		
	      String info = "Car built: \n";
	        info += "Type of car: " + type + "\n";
	        info += "Count of seats: " + seats + "\n";
	        info += "Engine: volume - " + engine.getVolume() + "; mileage - " + engine.getMileage() + "\n";
	        info += "Transmission: " + transmission + "\n";
	        if (this.tripComputer != null) {
	            info += "Trip Computer: Functional" + "\n";
	        } else {
	            info += "Trip Computer: N/A" + "\n";
	        }
	        if (this.gpsNavigator != null) {
	            info += "GPS Navigator: Functional" + "\n";
	        } else {
	            info += "GPS Navigator: N/A" + "\n";
	        }
	        return info;
	}
    
    
    
}
