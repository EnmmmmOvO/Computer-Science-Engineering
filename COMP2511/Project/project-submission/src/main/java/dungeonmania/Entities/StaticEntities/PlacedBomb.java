package dungeonmania.Entities.StaticEntities;

import java.util.Iterator;
import java.util.List;

import dungeonmania.Entities.Entity;
import dungeonmania.MapGenerator.MapGenerator;
import dungeonmania.util.Direction;
import dungeonmania.util.Position;

public class PlacedBomb extends StaticEntities {

    public PlacedBomb(int x, int y) {
        super(x, y, 1, "bomb_placed", false);
    }

    @Override
    public void update(MapGenerator mapGenerator, Direction direction) {
        List<Entity> elist = mapGenerator.getEntities();
        // if active switch is adjacent
        boolean explode = false;
        for (Entity entity : elist) {
            if (entity instanceof FloorSwitch) {
                FloorSwitch s = (FloorSwitch) entity;
                if (Position.isAdjacent(s.getPosition(), this.getPosition()) && s.isActive()) {
                    explode = true;
                    break;
                }
            }
        }
        if (explode) {
            Iterator<Entity> it = mapGenerator.getEntities().iterator();
            while(it.hasNext()){
                Entity e = it.next();
                if (Position.isAdjacent(e.getPosition(), this.getPosition())) {
                    it.remove();
                }
            }
            mapGenerator.removeEntity(this);

        }

    }

    @Override
    public Boolean isObstacle() {
        return true;
    }

    @Override
    public void interact(MapGenerator mapGenerator) {
        return;

    }

    @Override
    public Boolean isInteractable() {
        return false;
    }
}
