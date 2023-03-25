package degree;

import org.json.JSONObject;

import java.io.*;
public class Start {
    public static void main(String[] args) {
        JSONObject jsonObject = new DegreeDistribution().distribute("Week02/lab02/src/degree/data/degreesDocumentation.json",
                "Week02/lab02/src/degree/data/studentsDocumentation.json");

        try {
            File json = new File("Week02/lab02/src/degree/data/egrees.json");
            json.createNewFile();
            String jsonString = jsonObject.toString();
            Writer write = new OutputStreamWriter(new FileOutputStream(json), "UTF-8");
            write.write(jsonString);
            write.flush();
            write.close();
        } catch (Exception e) {
            System.err.println(e);
        }

    }
}
