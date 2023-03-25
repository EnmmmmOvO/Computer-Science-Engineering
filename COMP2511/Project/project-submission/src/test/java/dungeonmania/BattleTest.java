package dungeonmania;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import org.junit.jupiter.api.Test;
import dungeonmania.response.models.DungeonResponse;
import dungeonmania.response.models.ItemResponse;
import dungeonmania.util.Direction;

public class BattleTest {

    @Test
    public void testBomb() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("bombTest", "standard");
        controller.tick(null, Direction.DOWN);
        controller.tick(null, Direction.RIGHT);
        DungeonResponse world = controller.tick(null, Direction.LEFT);
        for (ItemResponse item : world.getInventory()) {
            if (item.getType() == "bomb") {
                controller.tick(item.getId(), Direction.NONE);
            }
        }
        world = controller.tick(null, Direction.NONE);
        // assert the entities adjacent to bomb are destroyed
        assertTrue(world.getEntities().stream()
                .noneMatch(i -> i.getPosition().getX() == 0 && i.getPosition().getY() == 2));
        assertTrue(world.getEntities().stream()
                .noneMatch(i -> i.getPosition().getX() == 1 && i.getPosition().getY() == 3));
        assertTrue(world.getEntities().stream().anyMatch(i -> i.getType() == "player"));
    }

    @Test
    public void testSpiderBattle() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("battleTest", "standard");
        DungeonResponse world = controller.tick(null, Direction.LEFT);
        for (int i = 0; i < 10000; i++) {

            controller.tick(null, Direction.NONE);

        }
        assertTrue(!world.getEntities().stream().noneMatch(i -> i.getType() == "player")
                || world.getEntities().stream().noneMatch(i -> i.getType() == "spider"));
    }

    @Test
    public void testZombieBattle() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("battleTest", "standard");
        DungeonResponse world = controller.tick(null, Direction.UP);
        // assert the entities adjacent to bomb are destroyed
        assertTrue(!world.getEntities().stream().noneMatch(i -> i.getType() == "player")
                || world.getEntities().stream().noneMatch(i -> i.getType() == "zombie_toast"));
    }

    @Test
    public void testMercenaryBattle() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("battleTest", "standard");
        DungeonResponse world = controller.tick(null, Direction.LEFT);
        world = controller.tick(null, Direction.LEFT);
        // assert the entities adjacent to bomb are destroyed
        assertTrue(world.getEntities().stream().noneMatch(i -> i.getType() == "player")
                || world.getEntities().stream().noneMatch(i -> i.getType() == "mercenary"));
    }

    @Test
    public void testBattleWithInvPotion() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("battleTest", "standard");
        DungeonResponse world = controller.tick(null, Direction.RIGHT);
        for (ItemResponse item : world.getInventory()) {
            if (item.getType().equals("invincibility_potion")) {
                controller.tick(item.getId(), Direction.NONE);
            }
        }
        for (int i = 0; i < 15; i++) {
            System.out.println(controller.getCurrentMap().getPlayer().getVita());
            controller.tick(null, Direction.LEFT);
        }
        world = controller.tick(null, Direction.LEFT);
        // assert enemies are killed and player has full hp

        assertEquals(controller.getCurrentMap().getPlayer().getVita(),
                controller.getCurrentMap().getPlayer().getInitialVita() - 10);
    }
}
