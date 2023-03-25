package dungeonmania.Entities.CollectableEntities;

import dungeonmania.MapGenerator.MapGenerator;

public class InvincibilityPotion extends CollectableEntities {

    public InvincibilityPotion(int x, int y) {
        super(x, y, 0, "invincibility_potion");
    }

    @Override
    public void interact(MapGenerator mapGenerator) {
        return;
    }

}
