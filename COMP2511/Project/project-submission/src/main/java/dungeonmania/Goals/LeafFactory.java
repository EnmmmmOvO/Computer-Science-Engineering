package dungeonmania.Goals;

import dungeonmania.MapGenerator.MapGenerator;

public class LeafFactory {

    public static Goal newLeaf(String type, MapGenerator map) {
        Goal goal = null;

        if (type.equals("exit")) {
            goal = new GoalLeafExit(type, map);
        } else if (type.equals("treasure")) {
            goal = new GoalLeafTreasure(type, map);
        } else if (type.equals("boulders")) {
            goal = new GoalLeafBoulders(type, map);
        } else if (type.equals("enemies")) {
            goal = new GoalLeafEnemies(type, map);
        }

        return goal;
    }

}
