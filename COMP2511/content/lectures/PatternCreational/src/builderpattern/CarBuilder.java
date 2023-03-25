package builderpattern;

/**
 * Builder interface defines all possible ways to configure a product.
 */
public interface CarBuilder {
	
    void setType(Type type);
    void setSeats(int seats);
    void setEngine(Engine engine);
    void setTransmission(Transmission transmission);
    void setTripComputer(TripComputer tripComputer);
    void setGPSNavigator(GPSNavigator gpsNavigator);
    
}
