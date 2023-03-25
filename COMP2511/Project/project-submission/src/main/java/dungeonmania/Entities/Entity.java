package dungeonmania.Entities;

import dungeonmania.MapGenerator.MapGenerator;
import dungeonmania.util.Direction;
import dungeonmania.util.Position;

public interface Entity {

    public Position getPosition();

    public int getPositionX();

    public int getPositionY();

    public int getPositionLayer();

    public String getType();

    public String getId();

    public void setPosition(int x, int y, int layer);

    public void setPosition(Position position);

    public Boolean isObstacle();

    public Boolean isInteractable();

    public void move(Direction direction);

    public void update(MapGenerator mapGenerator, Direction direction);

    public void interact(MapGenerator mapGenerator);
}
