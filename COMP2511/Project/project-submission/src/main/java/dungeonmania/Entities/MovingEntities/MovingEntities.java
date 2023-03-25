package dungeonmania.Entities.MovingEntities;

import dungeonmania.Battle;
import dungeonmania.Entities.Entity;
import dungeonmania.MapGenerator.MapGenerator;
import dungeonmania.util.Direction;
import dungeonmania.util.Position;

public abstract class MovingEntities implements Entity, Battle {

    private Position position;
    private String Entityid;
    private String type;
    private final Boolean Obstacle = false;
    private Boolean isInteractable;

    public MovingEntities(int x, int y, int layer, String type, Boolean isInteractable) {
        this.position = new Position(x, y, layer);
        this.type = type;
        this.Entityid = type + " (" + x + " , " + y + ")";
        this.isInteractable = isInteractable;
    }

    public MovingEntities(int x, int y, int layer, String type, String id, Boolean isInteractable) {
        this.position = new Position(x, y, layer);
        this.type = type;
        this.Entityid = type + " (" + x + " , " + y + ")";
        this.isInteractable = isInteractable;
        this.Entityid = id;
    }

    public void move(Direction direction) {
        this.setPosition(this.getPosition().translateBy(direction));
    }

    @Override
    public abstract void update(MapGenerator mapGenerator, Direction direction);

    public abstract void interact(MapGenerator mapGenerator);

    public abstract void battle(MapGenerator mapGenerator, Battle enemy);

    public String getType() {
        return this.type;
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

    public void setIsInteractable(Boolean isInteractable) {
        this.isInteractable = isInteractable;
    }

    public void setEntityid(String entityid) {
        Entityid = entityid;
    }

    public Boolean isObstacle() {
        return Obstacle;
    }

    public Boolean isInteractable() {
        return isInteractable;
    }

}
