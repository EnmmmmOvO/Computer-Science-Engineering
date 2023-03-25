package hotel;

import java.time.LocalDate;

import org.json.JSONObject;

public interface Room {
    
    /**
     * Checks if the room is not booked out during the given time.
     * If so, creates a booking for the room at that time.
     * @param arrival
     * @param departure
     * @return The booking object if the booking succeeded, null if failed
     */
    public Booking book(LocalDate arrival, LocalDate departure);

    /**
     * @return A JSON object of the form:
     * {
     *  "bookings": [ each booking as a JSON object, in order of creation ],
     *  "type": the type of the room (standard, ensuite, penthouse)
     * }
     */
    public JSONObject toJSON();
    
    /**
     * Removes the given booking from the list of bookings.
     * If the booking isn't in the list of bookings, does nothing.
     * @param booking
     */
    public void removeBooking(Booking booking);

    /**
     * Changes the given booking to be from the updated arrival date to the updated departure date,
     * if and only if the room is available between the updated times.
     * Note that a room being unavailable does NOT include the time of the original booking.
     * 
     * If the room is not available between the updated times, the change fails
     * and the room's booking list remains as it was before the function was called unchanged.
     * @param booking
     * @param arrival
     * @param departure
     */
    public Booking changeBooking(Booking booking, LocalDate arrival, LocalDate departure);

    /**
     * Prints a welcome message to the guest staying in the room.
     */
    public void printWelcomeMessage();

}