package dungeonmania.Entities.StaticEntities;

import java.util.List;

import dungeonmania.Entities.Entity;
import dungeonmania.Entities.EntityFactory;
import dungeonmania.Entities.CollectableEntities.Bow;
import dungeonmania.Entities.CollectableEntities.Sword;
import dungeonmania.MapGenerator.MapGenerator;
import dungeonmania.exceptions.InvalidActionException;
import dungeonmania.util.Direction;
import dungeonmania.util.Position;

public class ZombieToastSpawner extends StaticEntities {
    public static int tickTimes = 0;
    public Direction spawnDirection;

    private Boolean isInteractable = true;

    public ZombieToastSpawner(int x, int y) {
        super(x, y, 1, "zombie_toast_spawner", false);
    }

    @Override
    public void update(MapGenerator mapGenerator, Direction direction) {

        if (spawnDirection == null) {

            Position leftPosition = getPosition().translateBy(Direction.LEFT);
            Position rightPosition = getPosition().translateBy(Direction.RIGHT);
            Position topPosition = getPosition().translateBy(Direction.UP);
            Position bottomPosition = getPosition().translateBy(Direction.DOWN);

            if (mapGenerator.getEntities().stream().filter(e -> e.getPosition().equals(leftPosition))
                    .noneMatch(e -> e instanceof Wall)) {
                this.spawnDirection = Direction.LEFT;
            } else if (mapGenerator.getEntities().stream().filter(e -> e.getPosition().equals(rightPosition))
                    .noneMatch(e -> e instanceof Wall)) {
                this.spawnDirection = Direction.RIGHT;
            } else if (mapGenerator.getEntities().stream().filter(e -> e.getPosition().equals(topPosition))
                    .noneMatch(e -> e instanceof Wall)) {
                this.spawnDirection = Direction.UP;
            } else if (mapGenerator.getEntities().stream().filter(e -> e.getPosition().equals(bottomPosition))
                    .noneMatch(e -> e instanceof Wall)) {
                this.spawnDirection = Direction.DOWN;
            }

        }

        if (tickTimes % 20 == 0 && tickTimes > 0 && mapGenerator.getGameMode().equals("standard")) {

            Position newPosition = getPosition().translateBy(this.spawnDirection);
            Entity zombieToast = EntityFactory.newEntity("zombie_toast", newPosition.getX(), newPosition.getY(), null);

            mapGenerator.getEntities().add(zombieToast);
            mapGenerator.getEnemyList().add(zombieToast);

        } else if (tickTimes % 15 == 0 && tickTimes > 0 && mapGenerator.getGameMode().equals("hard")) {
            Position newPosition = getPosition().translateBy(this.spawnDirection);
            Entity zombieToast = EntityFactory.newEntity("zombie_toast", newPosition.getX(), newPosition.getY(), null);

            mapGenerator.getEntities().add(zombieToast);
            mapGenerator.getEnemyList().add(zombieToast);
        }

        tickTimes++;
    }

    @Override
    public void interact(MapGenerator curMap) {

        List<Entity> inventorys = curMap.getInventoryList();

        for (Entity e : inventorys) {
            if (e instanceof Bow || e instanceof Sword) {

                curMap.removeInventoryList(e);
                this.isInteractable = false;
                return;

            }
        }

        throw new InvalidActionException("have no weapon to destory a spawner");

    }

    public void setIsInteractable(Boolean isInteractable) {
        this.isInteractable = isInteractable;
    }

    @Override
    public Boolean isInteractable() {
        return isInteractable;
    }

}