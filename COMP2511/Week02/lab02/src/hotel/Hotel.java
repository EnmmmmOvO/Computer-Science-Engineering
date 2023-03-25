package hotel;

import java.io.*;
import java.time.LocalDate;
import java.util.*;

import org.json.JSONObject;

public class Hotel {

    private List<StandardRoom> standardRoomList;
    private List<PenthouseRoom> penthouseRoomList;
    private List<EnsuiteRoom> ensuiteRoomList;
    private String name;

    public Hotel(int size, String name) {
        this.name = name;
        standardRoomList = new ArrayList<>();
        penthouseRoomList = new ArrayList<>();
        ensuiteRoomList = new ArrayList<>();
        for (int loop = 0; loop < size; loop++) {
            standardRoomList.add(new StandardRoom());
            penthouseRoomList.add(new PenthouseRoom());
            ensuiteRoomList.add(new EnsuiteRoom());
        }
    }

    /**
     * Makes a booking in any available room with the given preferences.
     * 
     * @param arrival
     * @param departure
     * @param standard - does the client want a standard room?
     * @param ensuite - does the client want an ensuite room?
     * @param penthouse - does the client want a penthouse room?
     * @return If there were no available rooms for the given preferences, returns false.
     * Returns true if the booking was successful
     */
    public boolean makeBooking(LocalDate arrival, LocalDate departure, boolean standard, boolean ensuite, boolean penthouse) {
        // if customer prefer more than one room style, standard > ensuite > penthouse
        boolean finished = false;
        if (standard) {
            for (int loop = 0; loop < standardRoomList.size(); loop++)
                if (standardRoomList.get(loop).book(arrival, departure) != null) return true;
        }
        if (ensuite) {
            for (int loop = 0; loop < ensuiteRoomList.size(); loop++)
                if (ensuiteRoomList.get(loop).book(arrival, departure) != null) return true;
        }
        if (penthouse) {
            for (int loop = 0; loop < penthouseRoomList.size(); loop++)
                if (penthouseRoomList.get(loop).book(arrival, departure) != null) return true;
        }
        return false;
    }


    /**
     * @return A JSON Object of the form:
     * { "name": name, "rooms": [ each room as a JSON object, in order of creation ]}
     */
    public JSONObject toJSON() {
        JSONObject jsonObject = new JSONObject();
        JSONObject room = new JSONObject();
        int size = 0;
        for (int loop = 0; loop < standardRoomList.size(); loop++, size++)
            room.put("Room" + Integer.toString(size), standardRoomList.get(loop).toJSON());
        for (int loop = 0; loop < ensuiteRoomList.size(); loop++, size++)
            room.put("Room" + Integer.toString(size), ensuiteRoomList.get(loop).toJSON());
        for (int loop = 0; loop < penthouseRoomList.size(); loop++, size++)
            room.put("Room" + Integer.toString(size), penthouseRoomList.get(loop).toJSON());

        jsonObject.put("name", name);
        jsonObject.put("rooms", room);
        return jsonObject;
    }

    public static void main(String[] args) {
//        Scanner scanner = new Scanner(System.in);
//        System.out.print("Please input the name of the hotel");
//        String name = scanner.nextLine();
//        System.out.print("Please input the number of the room");
//        int size = Integer.parseInt(scanner.nextLine());
        int size = 1;
        String name = "Hilton";
        Hotel hotel = new Hotel(size, name);

        hotel.makeBooking(LocalDate.of(2022, 4, 1), LocalDate.of(2022,4,4),
                true, false, false);
        hotel.makeBooking(LocalDate.of(2022, 4, 3), LocalDate.of(2022,4,7),
                true, false, false);

        try {
            File json = new File("Week02/lab02/src/hotel/hotel.json");
            json.createNewFile();
            String jsonString = hotel.toJSON().toString();
            Writer write = new OutputStreamWriter(new FileOutputStream(json), "UTF-8");
            write.write(jsonString);
            write.flush();
            write.close();

        } catch (Exception e) {
            System.err.println(e);
        }


        
    }   
}