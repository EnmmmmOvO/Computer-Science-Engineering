package dungeonmania.Goals;

import dungeonmania.MapGenerator.MapGenerator;

public class GoalLeafEnemies extends GoalLeaf {

    public GoalLeafEnemies(String type, MapGenerator map) {
        super(type, map);
    }

    @Override
    public boolean pass() {
        return map.getEnemyList().size() == 0;
    }

}
