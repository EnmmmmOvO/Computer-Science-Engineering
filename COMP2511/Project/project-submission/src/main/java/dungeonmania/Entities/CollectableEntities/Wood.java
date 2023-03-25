package dungeonmania.Entities.CollectableEntities;

import dungeonmania.MapGenerator.MapGenerator;

public class Wood extends CollectableEntities {

    public Wood(int x, int y) {
        super(x, y, 0, "wood");
    }

    @Override
    public void interact(MapGenerator mapGenerator) {
        return;
    }

}
