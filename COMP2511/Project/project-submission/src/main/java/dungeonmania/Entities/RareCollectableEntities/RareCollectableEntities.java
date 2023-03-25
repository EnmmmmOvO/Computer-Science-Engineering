package dungeonmania.Entities.RareCollectableEntities;

import java.util.List;

import dungeonmania.Entities.Entity;
import dungeonmania.Entities.CharacterEntities.CharacterEntities;
import dungeonmania.Entities.StaticEntities.Wall;
import dungeonmania.MapGenerator.MapGenerator;
import dungeonmania.util.Direction;
import dungeonmania.util.Position;

public abstract class RareCollectableEntities implements Entity {

    private Position position;
    private String Entityid;
    private String type;
    private final Boolean isInteractable = false;

    public RareCollectableEntities(int x, int y, int layer, String type) {
        this.position = new Position(x, y, layer);
        this.type = type;
        this.Entityid = type + " (" + x + " , " + y + ")";
    }

    public void move(Direction direction) {
        return;
    }

    @Override
    public void update(MapGenerator mapGenerator, Direction direction) {

        List<Entity> elist = mapGenerator.getEntities();
        Entity collectable = null;
        Entity player = null;

        for (Entity e : elist) {
            if (e.equals(this)) {
                collectable = e;
            }
            if (e instanceof CharacterEntities) {
                player = e;
            }
        }

        Position p = player.getPosition().translateBy(direction);

        if (player.getPosition().translateBy(direction).equals(collectable.getPosition()) && mapGenerator.getEntities()
                .stream().filter(e -> e.getPosition().equals(p)).noneMatch(e -> e instanceof Wall)) {
            mapGenerator.addInventoryList(collectable);
            mapGenerator.removeEntity(collectable);
        }

    }

    public String getType() {
        return type;
    }

    public String getId() {
        return Entityid;
    }

    public Position getPosition() {
        return position;
    }

    public int getPositionX() {
        return getPosition().getX();
    }

    public int getPositionY() {
        return getPosition().getY();
    }

    public int getPositionLayer() {
        return getPosition().getLayer();
    }

    public void setPosition(int x, int y, int layer) {
        this.position = new Position(x, y, layer);
    }

    public void setPosition(Position newPosition) {
        this.position = newPosition;
    }

    @Override
    public Boolean isInteractable() {
        return isInteractable;
    }

    public Boolean isObstacle() {
        return false;
    }

}
