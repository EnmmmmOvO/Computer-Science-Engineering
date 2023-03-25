package dungeonmania;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import org.junit.jupiter.api.Test;

import dungeonmania.exceptions.InvalidActionException;
import dungeonmania.response.models.DungeonResponse;
import dungeonmania.response.models.EntityResponse;
import dungeonmania.util.Direction;

public class otherTest {

    @Test
    public void testUseKey() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("keyTest", "peaceful");
        controller.tick(null, Direction.RIGHT);
        controller.tick(null, Direction.RIGHT);
        DungeonResponse world = controller.tick(null, Direction.RIGHT);
        assertTrue(world.getEntities().stream()
                .anyMatch(e -> e.getType() == "player" && e.getPosition().getX() == 4 && e.getPosition().getY() == 1));
        assertTrue(world.getInventory().stream().noneMatch(i -> i.getType() == "key"));
    }

    @Test
    public void testWrongKey() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("keyTest", "peaceful");
        controller.tick(null, Direction.DOWN);
        controller.tick(null, Direction.RIGHT);
        controller.tick(null, Direction.RIGHT);
        controller.tick(null, Direction.UP);
        DungeonResponse world = controller.tick(null, Direction.RIGHT);
        assertTrue(world.getEntities().stream()
                .anyMatch(e -> e.getType() == "player" && e.getPosition().getX() == 3 && e.getPosition().getY() == 1));
        assertTrue(world.getInventory().stream().anyMatch(i -> i.getType() == "key"));
    }

    @Test
    public void testCannotPickUpTwoKey() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("keyTest", "peaceful");
        controller.tick(null, Direction.DOWN);
        controller.tick(null, Direction.RIGHT);
        DungeonResponse world = controller.tick(null, Direction.UP);
        long keyCount = world.getInventory().stream().filter(e -> e.getType() == "key").count();
        assertEquals(keyCount, 1L);
        controller.tick(null, Direction.RIGHT);
        world = controller.tick(null, Direction.RIGHT);
        assertTrue(world.getEntities().stream()
                .anyMatch(e -> e.getType() == "player" && e.getPosition().getX() == 3 && e.getPosition().getY() == 1));
        controller.tick(null, Direction.DOWN);
        world = controller.tick(null, Direction.RIGHT);
        assertTrue(world.getEntities().stream()
                .anyMatch(e -> e.getType() == "player" && e.getPosition().getX() == 4 && e.getPosition().getY() == 2));
        assertTrue(world.getInventory().stream().noneMatch(i -> i.getType() == "key"));
    }

    @Test
    public void testBoulderMove() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("StaticEntityTest", "standard");
        controller.tick(null, Direction.RIGHT);
        DungeonResponse world = controller.tick(null, Direction.DOWN);
        // Check player move to the boulder's position
        assertTrue(world.getEntities().stream()
                .anyMatch(e -> e.getType() == "player" && e.getPosition().getX() == 2 && e.getPosition().getY() == 2));
        // Try push boulder to the wall
        world = controller.tick(null, Direction.DOWN);
        assertTrue(world.getEntities().stream()
                .anyMatch(e -> e.getType() == "player" && e.getPosition().getX() == 2 && e.getPosition().getY() == 2));
        // Try push 2 boulders
        controller.tick(null, Direction.LEFT);
        world = controller.tick(null, Direction.DOWN);
        assertTrue(world.getEntities().stream()
                .anyMatch(e -> e.getType() == "player" && e.getPosition().getX() == 1 && e.getPosition().getY() == 3));
        world = controller.tick(null, Direction.RIGHT);
        assertTrue(world.getEntities().stream()
                .anyMatch(e -> e.getType() == "player" && e.getPosition().getX() == 1 && e.getPosition().getY() == 3));
    }

    @Test
    public void testSinglePortal() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("portalTest", "peaceful");
        DungeonResponse world = controller.tick(null, Direction.RIGHT);
        assertTrue(world.getEntities().stream()
                .anyMatch(e -> e.getType() == "player" && e.getPosition().getX() == 5 && e.getPosition().getY() == 0));

    }

    @Test
    public void testSecondPortal() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("portalTest", "peaceful");
        controller.tick(null, Direction.DOWN);
        DungeonResponse world = controller.tick(null, Direction.RIGHT);
        assertTrue(world.getEntities().stream()
                .anyMatch(e -> e.getType() == "player" && e.getPosition().getX() == 5 && e.getPosition().getY() == 1));

    }

    // Sunstone tests
    @Test
    public void testBuildShieldWithSunStone() {
        DungeonManiaController controller = new DungeonManiaController();
        // Collect materials
        controller.newGame("sunstoneTest", "standard");

        controller.tick(null, Direction.RIGHT);
        controller.tick(null, Direction.DOWN);
        controller.tick(null, Direction.DOWN);
        DungeonResponse world = controller.build("shield");
        assertTrue(world.getInventory().stream().anyMatch(item -> item.getType() == "shield"));

    }

    @Test
    public void testTreasureGoalWithSunStone() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("_treasureTest", "standard");
        DungeonResponse world = controller.tick(null, Direction.RIGHT);
        assertTrue(world.getGoals() == "");

    }

    @Test
    public void testOpenDoorWithSunStone() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("sunstoneTest", "standard");
        controller.tick(null, Direction.RIGHT);
        DungeonResponse world = controller.tick(null, Direction.RIGHT);
        assertTrue(world.getEntities().stream()
                .anyMatch(e -> e.getType() == "player" && e.getPosition().getX() == 3 && e.getPosition().getY() == 1));
        assertTrue(world.getInventory().stream().anyMatch(item -> item.getType() == "sun_stone"));

    }

    // Sceptre tests

    @Test
    public void testBuildSceptre() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("sunstoneTest", "standard");
        controller.tick(null, Direction.RIGHT);
        controller.tick(null, Direction.DOWN);
        controller.tick(null, Direction.LEFT);
        DungeonResponse world = controller.build("sceptre");
        assertTrue(world.getInventory().stream().anyMatch(item -> item.getType() == "sceptre"));

    }

    @Test
    public void testMindControlMercenary() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("mindControlTest", "standard");

        DungeonResponse world = controller.tick(null, Direction.RIGHT);
        for (EntityResponse e : world.getEntities()) {
            if (e.getType() == "mercenary") {
                assertThrows(InvalidActionException.class, () -> {
                    controller.interact(e.getId());
                });

            }
        }
    }

    @Test
    public void testBuildMidnight() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("sunstoneTest", "standard");
        controller.tick(null, Direction.RIGHT);
        controller.tick(null, Direction.RIGHT);
        controller.tick(null, Direction.RIGHT);
        DungeonResponse world = controller.build("midnight_armour");
        assertTrue(world.getInventory().stream().anyMatch(item -> item.getType() == "midnight_armour"));

    }

    @Test

    public void testAnduril() {

        DungeonManiaController controller = new DungeonManiaController();

        controller.newGame("sunstoneTest", "standard");

        controller.tick(null, Direction.DOWN);

        DungeonResponse world = controller.tick(null, Direction.DOWN);

        assertTrue(world.getInventory().stream().anyMatch(item -> item.getType() == "anduril"));

    }
}
