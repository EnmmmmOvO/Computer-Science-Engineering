package dungeonmania.Entities.StaticEntities;

import dungeonmania.Entities.Entity;
import dungeonmania.MapGenerator.MapGenerator;
import dungeonmania.util.Direction;
import dungeonmania.util.Position;

public abstract class StaticEntities implements Entity {

    private Position position;
    private String Entityid;
    private String type;
    private Boolean Obstacle;

    public StaticEntities(int x, int y, int layer, String type, Boolean Obstacle) {
        this.position = new Position(x, y, layer);
        this.type = type;
        this.Entityid = type + " (" + x + " , " + y + ")";
        this.Obstacle = Obstacle;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        StaticEntities other = (StaticEntities) obj;

        return position == other.position;
    }

    public void move(Direction direction) {
        this.setPosition(this.getPosition().translateBy(direction));
    }

    public abstract void update(MapGenerator mapGenerator, Direction direction);

    public abstract void interact(MapGenerator mapGenerator);

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

    public String getType() {
        return type;
    }

    public String getId() {
        return Entityid;
    }

    public void setPosition(int x, int y, int layer) {
        this.position = new Position(x, y, layer);
    }

    public void setPosition(Position newPosition) {
        this.position = newPosition;
    }

    public void setObstacle(Boolean obstacle) {
        Obstacle = obstacle;
    }

    public Boolean isObstacle() {
        return Obstacle;
    }

    public void setType(String type) {
        this.type = type;
    }
}
