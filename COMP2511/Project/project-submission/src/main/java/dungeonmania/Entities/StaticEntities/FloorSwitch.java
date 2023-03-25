package dungeonmania.Entities.StaticEntities;

import java.util.List;

import dungeonmania.Entities.Entity;
import dungeonmania.MapGenerator.MapGenerator;
import dungeonmania.util.Direction;

public class FloorSwitch extends StaticEntities {
    private boolean active;

    public void setActive(boolean active) {
        this.active = active;
    }

    public FloorSwitch(int x, int y) {
        super(x, y, 1, "switch", false);
    }

    @Override
    public void update(MapGenerator mapGenerator, Direction direction) {
        List<Entity> elist = mapGenerator.getEntities();
        for (Entity entity : elist) {
            if (entity instanceof Boulder) {
                if (entity.getPosition().equals(this.getPosition())) {
                    this.setActive(true);
                    return;
                }
            }
        }
        return;
    }

    @Override
    public void interact(MapGenerator mapGenerator) {
        return;
    }

    public boolean isActive() {
        return this.active;
    }

    @Override
    public Boolean isInteractable() {
        return false;
    }

}
