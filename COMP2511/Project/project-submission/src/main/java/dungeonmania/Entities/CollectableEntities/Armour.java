package dungeonmania.Entities.CollectableEntities;

import dungeonmania.MapGenerator.MapGenerator;

public class Armour extends CollectableEntities {

    public Armour(int x, int y) {
        super(x, y, 0, "armour");
    }

    @Override
    public void interact(MapGenerator mapGenerator) {
        return;
    }

}
