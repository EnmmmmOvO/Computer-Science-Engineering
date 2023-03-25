package dungeonmania.Entities.CollectableEntities;

import dungeonmania.MapGenerator.MapGenerator;

public class HealthPotion extends CollectableEntities {

    public HealthPotion(int x, int y) {
        super(x, y, 0, "health_potion");
    }

    @Override
    public void interact(MapGenerator mapGenerator) {
        return;
    }

}
