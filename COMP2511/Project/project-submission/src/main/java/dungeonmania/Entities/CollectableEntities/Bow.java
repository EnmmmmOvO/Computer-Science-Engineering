package dungeonmania.Entities.CollectableEntities;

import java.util.ArrayList;
import java.util.List;

import dungeonmania.Entities.Entity;
import dungeonmania.Entities.EntityFactory;
import dungeonmania.MapGenerator.MapGenerator;

public class Bow extends CollectableEntities {

    public Bow(int x, int y) {
        super(x, y, 0, "bow");
    }

    public static void build(MapGenerator map, String buildable) {
        List<Entity> tempinventoryList = new ArrayList<>(map.getInventoryList());
        int woodcounter = 0;
        int arrowcounter = 0;
        for (Entity e : map.getInventoryList()) {
            if (e instanceof Wood && woodcounter < 1) {

                tempinventoryList.remove(e);
                woodcounter += 1;
            } else if (e instanceof Arrows && arrowcounter < 3) {
                tempinventoryList.remove(e);
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
