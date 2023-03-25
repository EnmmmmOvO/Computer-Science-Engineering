package dungeonmania.Entities.CollectableEntities;

import java.util.ArrayList;
import java.util.List;

import dungeonmania.Entities.Entity;
import dungeonmania.Entities.EntityFactory;
import dungeonmania.MapGenerator.MapGenerator;

public class MidnightArmour extends CollectableEntities {

    public MidnightArmour(int x, int y) {
        super(x, y, 0, "midnight_armour");
    }

    public static void build(MapGenerator map, String buildable) {
        List<Entity> tempinventoryList = new ArrayList<>(map.getInventoryList());
        int armourCounter = 0;
        int sunStoneCounter = 0;
        for (Entity e : map.getInventoryList()) {
            if (e instanceof Armour && armourCounter < 1) {
                tempinventoryList.remove(e);
                armourCounter += 1;
            } else if (e instanceof SunStone && sunStoneCounter < 1) {
                tempinventoryList.remove(e);
                sunStoneCounter += 1;
            }
        }
        map.setInventoryList(tempinventoryList);
        map.addInventoryList(EntityFactory.newEntity(buildable, -1, -1, null));
        map.removeBuildableSet(buildable);
    }

    @Override
    public void interact(MapGenerator mapGenerator) {
        return;

    }

}
