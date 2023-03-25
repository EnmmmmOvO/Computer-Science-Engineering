package dungeonmania.Goals;

import dungeonmania.Entities.Entity;
import dungeonmania.Entities.CollectableEntities.SunStone;
import dungeonmania.Entities.CollectableEntities.Treasure;
import dungeonmania.MapGenerator.MapGenerator;

public class GoalLeafTreasure extends GoalLeaf {

    public GoalLeafTreasure(String type, MapGenerator map) {
        super(type, map);
    }

    @Override
    public boolean pass() {

        for (Entity e : map.getEntities()) {
            if (e instanceof Treasure || e instanceof SunStone) {
                return false;
            }
        }

        return true;

    }

}
