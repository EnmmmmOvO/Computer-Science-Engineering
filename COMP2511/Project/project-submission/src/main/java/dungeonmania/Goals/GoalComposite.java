package dungeonmania.Goals;

import java.util.ArrayList;
import java.util.List;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import dungeonmania.MapGenerator.MapGenerator;

public class GoalComposite implements Goal {

    private String logic;
    private MapGenerator map;

    private List<Goal> goals = new ArrayList<>();
    private List<Goal> returngoals = new ArrayList<>();

    public GoalComposite(MapGenerator map, JsonObject goalJson) {

        this.map = map;
        this.logic = goalJson.get("goal").toString().substring(1, goalJson.get("goal").toString().length() - 1);

        JsonArray subGoals = goalJson.getAsJsonArray("subgoals");

        for (JsonElement json : subGoals) {

            JsonObject jsonObj = (JsonObject) json;

            if (this.map.isLeaf(jsonObj)) {

                Goal goal = LeafFactory.newLeaf(
                        jsonObj.get("goal").toString().substring(1, jsonObj.get("goal").toString().length() - 1), map);

                goals.add(goal);
                returngoals.add(goal);

            } else {

                goals.add(new GoalComposite(map, jsonObj));
                returngoals.add(new GoalComposite(map, jsonObj));

            }
        }

    }

    @Override
    public String toString() {

        String output = "";
        List<String> strings = new ArrayList<>();

        for (Goal goal : returngoals) {

            if (goal.toString().equals("")) {
                continue;
            }

            strings.add(goal.toString());

        }

        output = String.join(" " + this.logic + " ", strings);

        return output;

    }

    @Override
    public boolean pass() {

        int num = 0;

        for (Goal goal : goals) {
            if (goal.pass()) {
                num++;
                returngoals.remove(goal);
            }
        }

        if (this.logic.equals("AND")) {
            return num == goals.size();
        } else {
            return num >= 1;
        }

    }

}
