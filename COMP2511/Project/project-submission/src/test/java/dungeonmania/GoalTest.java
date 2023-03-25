package dungeonmania;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import org.junit.jupiter.api.Test;

import dungeonmania.response.models.DungeonResponse;
import dungeonmania.util.Direction;

public class GoalTest {
    @Test
    public void testGoalExit() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("exitTest", "standard");
        DungeonResponse world = controller.tick(null, Direction.UP);
        assertTrue(world.getGoals() == "");
    }

    @Test
    public void testGoalTreasure() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("treasureTest", "standard");
        DungeonResponse world = controller.tick(null, Direction.DOWN);
        assertTrue(world.getGoals() == "");
    }

    @Test
    public void testGoalBoulder() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("boulderTest", "standard");
        DungeonResponse world = controller.tick(null, Direction.DOWN);
        assertTrue(world.getGoals() == "");
    }

    @Test
    public void testGoalEnemy() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("enemyTest", "standard");
        DungeonResponse world = controller.tick(null, Direction.LEFT);
        // how to kill all the spiders?
        assertEquals(world.getGoals(), ":enemies");
    }

    @Test
    public void testAllGoals() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("allGoalTest", "standard");
        // Try to exit before complete other goals
        DungeonResponse world = controller.tick(null, Direction.DOWN);
        assertTrue(world.getGoals() != "");
        controller.tick(null, Direction.DOWN);

        controller.tick(null, Direction.DOWN);
        controller.tick(null, Direction.RIGHT);
        controller.tick(null, Direction.RIGHT);
        controller.tick(null, Direction.UP);
        controller.tick(null, Direction.LEFT);
        controller.tick(null, Direction.LEFT);
        world = controller.tick(null, Direction.UP);

        assertTrue(world.getGoals().equals(""));
    }

    @Test
    public void testAnyGoalsExit() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("anyGoalTest", "standard");
        DungeonResponse world = controller.tick(null, Direction.UP);
        assertTrue(world.getGoals() == "");
    }

    @Test
    public void testGoalTreasureNoTreasure() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("_treasureTest", "standard");
        DungeonResponse world = controller.tick(null, Direction.RIGHT);
        assertTrue(world.getGoals() == "");
    }
}
