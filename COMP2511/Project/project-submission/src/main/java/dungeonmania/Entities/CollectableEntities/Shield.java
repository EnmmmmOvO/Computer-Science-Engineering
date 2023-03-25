package dungeonmania.Entities.CollectableEntities;

import java.util.ArrayList;
import java.util.List;

import dungeonmania.Entities.Entity;
import dungeonmania.Entities.EntityFactory;
import dungeonmania.MapGenerator.MapGenerator;

public class Shield extends CollectableEntities {

    public Shield(int x, int y) {
        super(x, y, 0, "shield");
    }

    public static void build(MapGenerator map, String buildable) {
        List<Entity> tempinventoryList = new ArrayList<>(map.getInventoryList());
        int woodcounter = 0;
        int TreasureOrKey = 0;
        for (Entity e : map.getInventoryList()) {
            if (e instanceof Wood && woodcounter < 2) {
                tempinventoryList.remove(e);
                woodcounter += 1;
            } else if (((e instanceof Treasure || e instanceof SunStone) || e instanceof Key) && TreasureOrKey < 1) {
                tempinventoryList.remove(e);
                TreasureOrKey += 1;
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
