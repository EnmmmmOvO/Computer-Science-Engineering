package dungeonmania.Entities.StaticEntities;

import dungeonmania.MapGenerator.MapGenerator;
import dungeonmania.util.Direction;

public class Wall extends StaticEntities {

    public Wall(int x, int y) {
        super(x, y, 1, "wall", true);
    }

    @Override
    public void update(MapGenerator mapGenerator, Direction direction) {
        return;
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
