package dungeonmania.Entities.RareCollectableEntities;

import dungeonmania.MapGenerator.MapGenerator;

public class TheOneRing extends RareCollectableEntities {

    public TheOneRing(int x, int y) {
        super(x, y, 2, "one_ring");
    }

    @Override
    public void interact(MapGenerator mapGenerator) {
        return;
    }

}
