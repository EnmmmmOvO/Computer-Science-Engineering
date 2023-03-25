package degree;

import org.json.JSONArray;
import org.json.JSONObject;


import java.util.*;

public class Students {
    private String name;
    private double score;
    private int offer;
    private Preferences preferences;
    private Preferences end;

    private class Preferences {
        double score;
        int code;
        Preferences next;

        Preferences (double score, int code) {
            this.code = code;
            this.score = score;
            next = null;
        }
    }

    public Students(String name, double score, JSONArray preferenceArray) {
        this.name = name;
        this.score = score;
        Iterator<Object> it = preferenceArray.iterator();
        while (it.hasNext()) {
            String temp = (String) it.next();
            int code = 0;
            double addScore = 0;
            try {
                code = Integer.parseInt(temp);
            } catch (Exception e) {
                StringBuilder stringBuilder = new StringBuilder();
                int loop = 0;
                for (; temp.charAt(loop) != '+'; loop++) stringBuilder.append(temp.charAt(loop));
                code = Integer.parseInt(stringBuilder.toString());
                for (loop++, stringBuilder = new StringBuilder() ; loop < temp.length(); loop++)
                    stringBuilder.append(temp.charAt(loop));
                addScore = Double.parseDouble(stringBuilder.toString());
            } finally {
                Preferences newPer = new Preferences(addScore, code);
                if (preferences == null) {
                    end = newPer;
                    preferences = newPer;
                } else {
                    end.next = newPer;
                    end = newPer;
                }
            }
        }
        offer = preferences.code;
    }
    public String getName() {
        return name;
    }

    public int getOffer() {
        return offer;
    }

    public double getHighScore() {
        return preferences != null ? score + preferences.score : -1;
    }

    public double getScore() {
        return score;
    }

    public void removeOffer() {
        if (preferences.next == null) {
            preferences = null;
            end = null;
            offer = -1;
        } else if (preferences != null) {
            preferences = preferences.next;
            offer = preferences.code;
        }
    }

    public JSONObject toJSON() {
        JSONObject jsonObject = new JSONObject();
        jsonObject.put("name", name);
        jsonObject.put("score", score);
        jsonObject.put("offer", offer > 0 ? offer : "-");
        return jsonObject;
    }
}
