package dungeonmania.Entities.StaticEntities;

import dungeonmania.MapGenerator.MapGenerator;
import dungeonmania.util.Direction;

public class Door extends StaticEntities {
    private int keyType;

    public Door(int x, int y) {
        super(x, y, 0, "door", true);
    }

    public void setKeyType(int keyType) {
        this.keyType = keyType;
    }

    public int getKeyType() {
        return keyType;
    }

    @Override
    public void setObstacle(Boolean obstacle) {
        super.setObstacle(obstacle);
    }

    @Override
    public void update(MapGenerator mapGenerator, Direction direction) {

        return;
    }

    @Override
    public Boolean isInteractable() {

        return false;
    }

    @Override
    public void interact(MapGenerator mapGenerator) {
        return;

    }
}