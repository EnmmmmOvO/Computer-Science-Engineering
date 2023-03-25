package dungeonmania.Entities.RareCollectableEntities;

import dungeonmania.MapGenerator.MapGenerator;

public class Anduril extends RareCollectableEntities {
    public Anduril(int x, int y) {
        super(x, y, 2, "anduril");
    }

    @Override
    public void interact(MapGenerator mapGenerator) { }
}
