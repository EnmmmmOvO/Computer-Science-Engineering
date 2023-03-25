package dungeonmania.Entities.StaticEntities;

import dungeonmania.MapGenerator.MapGenerator;
import dungeonmania.util.Direction;

public class Exit extends StaticEntities {

    public Exit(int x, int y) {
        super(x, y, 1, "exit", false);
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