package degree;

import java.io.*;
import java.util.*;

import org.json.JSONArray;
import org.json.JSONObject;
import org.apache.commons.io.FileUtils;

public class DegreeDistribution {

    public JSONObject distribute(String degreesFilename, String studentsFilename) {
        JSONObject newJSON = new JSONObject(new LinkedHashMap());
        JSONArray degreeJSON = new JSONArray();
        JSONArray studentJSON = new JSONArray();

        Map<Integer, Degrees> degree = new HashMap<Integer, Degrees>();
        Map<Double, Students> studentsMap = new HashMap<>();
        Double[] studentsScore = null;
        int[] degreeCode = null;
        ArrayList<Students> students = new ArrayList<>();

        try {
            Iterator<Object> it = new JSONArray(FileUtils.readFileToString(new File(degreesFilename), "UTF-8")).iterator();
            int[] tempArray = new int[99];
            int degreeSize = 0;
            while (it.hasNext()) {
                JSONObject temp = (JSONObject) it.next();
                degree.put(temp.getInt("code"), new Degrees(temp.getInt("code"),
                        temp.getString("name"), temp.getString("institution"), temp.getInt("places")));
                tempArray[degreeSize] = temp.getInt("code");
                degreeSize++;
            }
            degreeCode = new int[degreeSize];
            for (int loop = 0; loop < degreeSize; loop++) degreeCode[loop] = tempArray[loop];
            Arrays.sort(degreeCode);

            Double[] tempDoubleArray = new Double[99];
            it = new JSONArray(FileUtils.readFileToString(new File(studentsFilename), "UTF-8")).iterator();
            int studentSize = 0;
            while (it.hasNext()) {
                JSONObject temp = (JSONObject) it.next();
                Students s = new Students(temp.getString("name"),
                        temp.getDouble("score"), temp.getJSONArray("preferences"));
                students.add(s);
                double tempScore = temp.getDouble("score");
                while (studentsMap.get(tempScore) != null) {
                    if (studentsMap.get(tempScore).getName().compareTo(s.getName()) < 0) {
                        Students tempStudent = studentsMap.get(tempScore);
                        studentsMap.put(tempScore, s);
                        s = tempStudent;
                    }
                    tempScore += 0.0001;
                }
                studentsMap.put(tempScore, s);
                tempDoubleArray[studentSize] = tempScore;
                studentSize++;
            }
            studentsScore = new Double[studentSize];
            for (int loop = 0; loop < studentSize; loop++) studentsScore[loop] = tempDoubleArray[loop];
            Arrays.sort(studentsScore);
        } catch (Exception e) {
            System.out.println(e);
        }


        while (students.size() != 0) {
            if (students.get(0).getOffer() == -1) {
                students.remove(0);
                continue;
            }
            Students s = degree.get(students.get(0).getOffer()).addStudent(students.get(0));
            if (s == null)
                students.remove(0);
            else
                students.add(s);
        }

        for (int loop = 0; loop < degreeCode.length; loop++) degreeJSON.put(degree.get(degreeCode[loop]).toJSON());
        for (int loop = studentsScore.length - 1; loop >= 0; loop--) {
            studentJSON.put(studentsMap.get(studentsScore[loop]).toJSON());
        }

        newJSON.put("degrees", degreeJSON);
        newJSON.put("students", studentJSON);
        return newJSON;
    }
}