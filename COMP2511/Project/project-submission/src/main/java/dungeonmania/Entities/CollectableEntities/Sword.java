package dungeonmania.Entities.CollectableEntities;

import dungeonmania.MapGenerator.MapGenerator;

public class Sword extends CollectableEntities {

    public Sword(int x, int y) {
        super(x, y, 0, "sword");
    }

    @Override
    public void interact(MapGenerator mapGenerator) {
        return;
    }

}
