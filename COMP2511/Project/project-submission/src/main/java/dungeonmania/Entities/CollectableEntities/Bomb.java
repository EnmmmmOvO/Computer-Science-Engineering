package dungeonmania.Entities.CollectableEntities;

import dungeonmania.MapGenerator.MapGenerator;

public class Bomb extends CollectableEntities {

    public Bomb(int x, int y) {
        super(x, y, 0, "bomb");
    }

    @Override
    public void interact(MapGenerator mapGenerator) {
        return;
    }
}
