package dungeonmania.Entities.CollectableEntities;

import dungeonmania.MapGenerator.MapGenerator;

public class InvisibilityPotion extends CollectableEntities {

    public InvisibilityPotion(int x, int y) {
        super(x, y, 0, "invisibility_potion");
    }

    @Override
    public void interact(MapGenerator mapGenerator) {
        return;
    }

}
