package hotel;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;

import org.json.JSONObject;

public class EnsuiteRoom implements Room {

    private List<Booking> bookings = new ArrayList<Booking>();

    @Override
    public Booking book(LocalDate arrival, LocalDate departure) {
        for (Booking booking : bookings) {
            if (booking.overlaps(arrival, departure)) {
                return null;
            }
        }

        Booking booking = new Booking(arrival, departure);
        bookings.add(booking);
        this.printWelcomeMessage();
        return booking;
    }

    @Override
    public JSONObject toJSON() {
        JSONObject jsonObject = new JSONObject();
        JSONObject ensuiteRoom = new JSONObject();
        for (int loop = 0; loop < bookings.size(); loop++)
            ensuiteRoom.put(Integer.toString(loop), bookings.get(loop).toJSON());
        jsonObject.put("bookings", ensuiteRoom);
        jsonObject.put("type", "Ensuite Room");
        return jsonObject;
    }

    @Override
    public void removeBooking(Booking booking) {
        bookings.remove(booking);
    }

    @Override
    public Booking changeBooking(Booking booking, LocalDate arrival, LocalDate departure) {
        for (int loop = 0; loop < bookings.size(); loop++) {
            if (!bookings.get(loop).equals(booking) && bookings.get(loop).overlaps(arrival, departure)) {
                return null;
            }
        }

        removeBooking(booking);
        Booking newBooking = new Booking(arrival, departure);
        bookings.add(newBooking);
        return booking;
    }

    @Override
    public void printWelcomeMessage() {
        System.out.println("Welcome to your beautiful ensuite room which overlooks the Sydney harbour. Enjoy your stay");
    }
    
}