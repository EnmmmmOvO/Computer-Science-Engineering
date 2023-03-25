package hotel;

import java.time.LocalDate;

import org.json.JSONObject;

public class Booking {
    
    LocalDate arrival;
    LocalDate departure;


    public Booking(LocalDate arrival, LocalDate departure) {
        this.arrival = arrival;
        this.departure = departure;
    }

    /**
     * @return a JSONObject of the form {"arrival": arrival, "departure": departure}
     */
    public JSONObject toJSON() {
        JSONObject booking = new JSONObject();
        booking.put("arrival", arrival);
        booking.put("departure", departure);

        return booking;
    }

    public boolean overlaps(LocalDate start, LocalDate end) {
        if (start.isAfter(arrival) || end.isBefore(departure)) return true;
        return false;
    }

}