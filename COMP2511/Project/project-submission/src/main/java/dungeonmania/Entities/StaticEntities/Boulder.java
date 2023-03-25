package dungeonmania.Entities.StaticEntities;

import java.util.List;

import dungeonmania.Entities.Entity;
import dungeonmania.Entities.CharacterEntities.CharacterEntities;
import dungeonmania.MapGenerator.MapGenerator;
import dungeonmania.util.Direction;

public class Boulder extends StaticEntities {

    public Boulder(int x, int y) {
        super(x, y, 2, "boulder", true);
    }

    @Override
    public void update(MapGenerator mapGenerator, Direction direction) {

        List<Entity> elist = mapGenerator.getEntities();
        Entity boulder = null;
        Entity player = null;

        for (Entity e : elist) {
            if (e.equals(this)) {
                boulder = e;
            }
            if (e instanceof CharacterEntities) {
                player = e;
            }
        }

        if (player.getPosition().translateBy(direction).equals(boulder.getPosition())) {

            for (Entity e : elist) {
                if (e.getPosition().equals(boulder.getPosition().translateBy(direction)) && e.isObstacle()) {
                    return;
                }
            }

            boulder.move(direction);

            for (Entity entity : elist) {

                if (entity instanceof FloorSwitch) {

                    FloorSwitch floorSwitch = (FloorSwitch) entity;

                    if (entity.getPosition().equals(this.getPosition())) {

                        floorSwitch.setActive(true);
                        break;

                    }

                }

            }

            player.move(direction);

        }
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