package dungeonmania.Goals;

import dungeonmania.Entities.Entity;
import dungeonmania.Entities.StaticEntities.FloorSwitch;
import dungeonmania.MapGenerator.MapGenerator;

public class GoalLeafBoulders extends GoalLeaf {

    public GoalLeafBoulders(String type, MapGenerator map) {
        super(type, map);
    }

    @Override
    public boolean pass() {

        for (Entity e : map.getEntities()) {
            if (e instanceof FloorSwitch) {
                FloorSwitch switch1 = (FloorSwitch) e;
                if (switch1.isActive() == false) {
                    return false;
                }
            }
        }

        return true;

    }

}
