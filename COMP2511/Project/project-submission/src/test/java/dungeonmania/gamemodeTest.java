package dungeonmania;

import static org.junit.jupiter.api.Assertions.assertTrue;
import org.junit.jupiter.api.Test;
import dungeonmania.response.models.DungeonResponse;
import dungeonmania.util.Direction;

public class gamemodeTest {
    @Test
    // test no one hurt in peaceful mode
    public void testpeaceful() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("battleTest", "peaceful");
        controller.tick(null, Direction.DOWN);
        controller.tick(null, Direction.RIGHT);
        controller.tick(null, Direction.LEFT);
        DungeonResponse world = controller.tick(null, Direction.LEFT);
        assertTrue(world.getEntities().stream().anyMatch(i -> i.getType() == "spider"));

        assertTrue(world.getEntities().stream().anyMatch(i -> i.getType() == "zombie_toast"));
        assertTrue(world.getEntities().stream().anyMatch(i -> i.getType() == "player"));
    }

    @Test
    public void testhardZombieSpawn() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("spawnerTest", "hard");
        for (int i = 0; i < 15; i++) {
            controller.tick(null, Direction.NONE);
        }
        DungeonResponse world = controller.tick(null, Direction.NONE);
        assertTrue(world.getEntities().stream().anyMatch(i -> i.getType() == "zombie_toast"));
    }

    @Test
    public void teststandardZombieSpawn() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("spawnerTest", "standard");
        for (int i = 0; i < 20; i++) {
            controller.tick(null, Direction.NONE);
        }
        DungeonResponse world = controller.tick(null, Direction.NONE);
        assertTrue(world.getEntities().stream().anyMatch(i -> i.getType() == "zombie_toast"));
    }

    @Test

    public void testHydraSpawn() {

        DungeonManiaController controller = new DungeonManiaController();

        controller.newGame("spawnerTest", "hard");

        for (int i = 0; i < 50; i++) {

            controller.tick(null, Direction.NONE);

        }

        DungeonResponse world = controller.tick(null, Direction.NONE);

        assertTrue(world.getEntities().stream().anyMatch(i -> i.getType() == "hydra"));

    }

    @Test

    public void testHydraSpawnInstandard() {

        DungeonManiaController controller = new DungeonManiaController();

        controller.newGame("spawnerTest", "standard");

        for (int i = 0; i < 50; i++) {

            controller.tick(null, Direction.NONE);

        }

        DungeonResponse world = controller.tick(null, Direction.NONE);

        assertTrue(world.getEntities().stream().noneMatch(i -> i.getType() == "hydra"));

    }
}
