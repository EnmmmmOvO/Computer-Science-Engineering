package dungeonmania.Entities.CollectableEntities;

import dungeonmania.MapGenerator.MapGenerator;

public class Arrows extends CollectableEntities {

    public Arrows(int x, int y) {
        super(x, y, 0, "arrow");
    }

    @Override
    public void interact(MapGenerator mapGenerator) {
        return;
    }
}
