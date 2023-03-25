package dungeonmania.Entities.CollectableEntities;

import java.util.ArrayList;
import java.util.List;

import dungeonmania.Entities.Entity;
import dungeonmania.Entities.EntityFactory;
import dungeonmania.MapGenerator.MapGenerator;

public class Sceptre extends CollectableEntities {

    public Sceptre(int x, int y) {
        super(x, y, 0, "sceptre");
    }

    public static void build(MapGenerator map, String buildable) {

        List<Entity> tempinventoryList = new ArrayList<>(map.getInventoryList());
        int woodOrArrow = 0;
        int woodCounter = 0;
        int arrowCounter = 0;
        int TreasureOrKey = 0;
        int sunStoneCounter = 0;
        Boolean costWood = true;
        for (Entity WoA : map.getInventoryList()) {
            if (WoA instanceof Arrows) {
                arrowCounter++;
                if (arrowCounter >= 2) {
                    costWood = false;
                }
            }
            if (WoA instanceof Wood) {
                woodCounter++;
            }

        }

        for (Entity e : map.getInventoryList()) {

            if (costWood) {
                if (e instanceof Wood && woodCounter > 0) {
                    tempinventoryList.remove(e);
                    woodCounter -= 1;
                }

            } else {
                if (e instanceof Arrows && arrowCounter > 0) {
                    tempinventoryList.remove(e);
                    arrowCounter -= 1;
                }
            }
            if ((e instanceof Treasure || e instanceof Key) && TreasureOrKey < 1) {
                tempinventoryList.remove(e);
                TreasureOrKey += 1;
            }
            if (e instanceof SunStone) {
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
