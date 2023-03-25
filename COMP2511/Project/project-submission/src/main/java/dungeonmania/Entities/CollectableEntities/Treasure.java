package dungeonmania.Entities.CollectableEntities;

import dungeonmania.MapGenerator.MapGenerator;

public class Treasure extends CollectableEntities {

    public Treasure(int x, int y) {
        super(x, y, 0, "treasure");
    }

    @Override
    public void interact(MapGenerator mapGenerator) {
        return;
    }

}
