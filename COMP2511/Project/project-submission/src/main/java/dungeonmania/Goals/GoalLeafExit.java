package dungeonmania.Goals;

import dungeonmania.Entities.Entity;
import dungeonmania.Entities.StaticEntities.Exit;
import dungeonmania.MapGenerator.MapGenerator;

public class GoalLeafExit extends GoalLeaf {

    public GoalLeafExit(String type, MapGenerator map) {
        super(type, map);
    }

    @Override
    public boolean pass() {

        for (Entity e : map.getEntities()) {
            if (e instanceof Exit) {
                if (!e.getPosition().equals(map.getPlayer().getPosition())) {
                    return false;
                }
            }
        }

        return true;

    }

}
