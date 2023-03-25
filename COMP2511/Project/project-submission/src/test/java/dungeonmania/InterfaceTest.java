package dungeonmania;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import org.junit.jupiter.api.Test;

import dungeonmania.response.models.DungeonResponse;
import dungeonmania.response.models.EntityResponse;
import dungeonmania.response.models.ItemResponse;
import dungeonmania.exceptions.InvalidActionException;
import dungeonmania.util.Direction;
import dungeonmania.util.Position;

import java.util.Arrays;
import java.util.List;

public class InterfaceTest {
    // tests for newGame
    @Test
    public void invalidGameMode() {
        DungeonManiaController dungeonManiaController = new DungeonManiaController();
        assertThrows(IllegalArgumentException.class, () -> {
            dungeonManiaController.newGame("advanced", "invalid");
        });
    }

    @Test
    public void invalidDungeonName() {
        DungeonManiaController dungeonManiaController = new DungeonManiaController();
        assertThrows(IllegalArgumentException.class, () -> {
            dungeonManiaController.newGame("invalid", "standard");
        });
    }

    @Test
    public void validGameMode() {
        DungeonManiaController dungeonManiaController = new DungeonManiaController();
        assertDoesNotThrow(() -> {
            dungeonManiaController.newGame("advanced", "standard");
        });
        assertDoesNotThrow(() -> {
            dungeonManiaController.newGame("advanced", "peaceful");
        });
        assertDoesNotThrow(() -> {
            dungeonManiaController.newGame("advanced", "hard");
        });
        assertDoesNotThrow(() -> {
            dungeonManiaController.newGame("boulders", "hard");
        });
    }

    // tests for saveGame
    @Test
    public void saveGameValid() {
        DungeonManiaController dungeonManiaController = new DungeonManiaController();
        DungeonResponse dungeonResponse = dungeonManiaController.newGame("advanced", "standard");
        assertDoesNotThrow(() -> {
            dungeonManiaController.saveGame(dungeonResponse.getDungeonId());
        });

    }

    @Test
    public void saveGameValidResponse() {
        DungeonManiaController dungeonManiaController = new DungeonManiaController();
        DungeonResponse dungeonResponse = dungeonManiaController.newGame("advanced", "standard");
        // saved game response
        DungeonResponse dungeonResponse2 = dungeonManiaController.saveGame(dungeonResponse.getDungeonId());
        assertEquals(dungeonResponse.getDungeonId(), dungeonResponse2.getDungeonId());
    }

    // tests for loadGame
    @Test
    public void loadGameValid() {
        DungeonManiaController dungeonManiaController = new DungeonManiaController();
        DungeonResponse dungeonResponse = dungeonManiaController.newGame("advanced", "standard");
        dungeonManiaController.saveGame(dungeonResponse.getDungeonId());

        assertDoesNotThrow(() -> {
            dungeonManiaController.loadGame(dungeonResponse.getDungeonId());
        });
    }

    @Test
    public void loadGameValidResponse() {
        DungeonManiaController dungeonManiaController = new DungeonManiaController();
        DungeonResponse dungeonResponse = dungeonManiaController.newGame("advanced", "standard");

        DungeonResponse dungeonResponse2 = dungeonManiaController.saveGame(dungeonResponse.getDungeonId());

        DungeonResponse dungeonResponse3 = dungeonManiaController.loadGame(dungeonResponse2.getDungeonId());

        assertEquals(dungeonResponse2.getDungeonId(), dungeonResponse3.getDungeonId());
    }

    @Test
    public void loadGameInValid() {
        DungeonManiaController dungeonManiaController = new DungeonManiaController();
        DungeonResponse dungeonResponse = dungeonManiaController.newGame("advanced", "standard");
        dungeonManiaController.saveGame(dungeonResponse.getDungeonId());
        assertThrows(IllegalArgumentException.class, () -> {
            dungeonManiaController.loadGame("invalid");
        });
    }

    // tests for allGames
    @Test
    public void allGamesTestSingle() {
        DungeonManiaController dungeonManiaController = new DungeonManiaController();
        DungeonResponse dungeonResponse = dungeonManiaController.newGame("advanced", "standard");
        DungeonResponse dungeonResponse2 = dungeonManiaController.saveGame(dungeonResponse.getDungeonId());
        List<String> gameList = dungeonManiaController.allGames();
        assertEquals(gameList, Arrays.asList(dungeonResponse2.getDungeonId().toString()));

    }

    @Test
    public void allGamesTestMultiple() {
        DungeonManiaController dungeonManiaController = new DungeonManiaController();
        DungeonResponse dungeonResponse = dungeonManiaController.newGame("advanced", "standard");
        DungeonResponse dungeonResponseSave1 = dungeonManiaController.saveGame(dungeonResponse.getDungeonId());

        DungeonResponse dungeonResponse2 = dungeonManiaController.newGame("advanced", "hard");
        DungeonResponse dungeonResponseSave2 = dungeonManiaController.saveGame(dungeonResponse2.getDungeonId());

        List<String> gameList = dungeonManiaController.allGames();
        // assertListAreEqualIgnoringOrder(gameList,
        // Arrays.asList(dungeonResponseSave1.getDungeonId(),
        // dungeonResponseSave2.getDungeonId()));
        assertTrue(gameList.size() == Arrays
                .asList(dungeonResponseSave1.getDungeonId(), dungeonResponseSave2.getDungeonId()).size()
                && Arrays.asList(dungeonResponseSave1.getDungeonId(), dungeonResponseSave2.getDungeonId())
                        .containsAll(gameList)
                && gameList.containsAll(
                        Arrays.asList(dungeonResponseSave1.getDungeonId(), dungeonResponseSave2.getDungeonId())));
    }

    // Tests for tick()
    @Test
    public void testTickMove() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("InterfaceTest1", "standard");
        assertDoesNotThrow(() -> {
            controller.tick(null, Direction.DOWN);
            controller.tick(null, Direction.UP);
            controller.tick(null, Direction.RIGHT);
            controller.tick(null, Direction.LEFT);
        });
    }

    @Test
    public void testPickBomb() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("InterfaceTest4", "standard");
        DungeonResponse world = controller.tick(null, Direction.DOWN);
        assertTrue(world.getInventory().stream().anyMatch(i -> i.getType() == "bomb"));

    }

    @Test
    public void testTickBomb() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("InterfaceTest4", "standard");
        DungeonResponse world = controller.tick(null, Direction.DOWN);
        assertTrue(world.getInventory().stream().anyMatch(i -> i.getType() == "bomb"));
        assertDoesNotThrow(() -> {
            for (ItemResponse item : world.getInventory()) {
                if (item.getType() == "bomb") {
                    controller.tick(item.getId(), Direction.NONE);
                }
            }
        });
        DungeonResponse used = controller.tick(null, Direction.NONE);
        assertTrue(used.getInventory().stream().noneMatch(i -> i.getType() == "bomb"));
        // Check bomb is placed on player's position
        Position playerPos = null, bombPos = null;
        for (EntityResponse e : used.getEntities()) {
            if (e.getType() == "player") {
                playerPos = e.getPosition();
            }
            if (e.getType() == "bomb_placed") {
                bombPos = e.getPosition();
            }
        }
        assertTrue(playerPos.equals(bombPos) && playerPos != null);
    }

    @Test
    public void testTickInvisibilityPotion() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("InterfaceTest4", "standard");
        controller.tick(null, Direction.DOWN);
        DungeonResponse world = controller.tick(null, Direction.DOWN);
        assertTrue(world.getInventory().stream().anyMatch(i -> i.getType() == "invisibility_potion"));
        assertDoesNotThrow(() -> {
            for (ItemResponse item : world.getInventory()) {
                if (item.getType() == "invisibility_potion") {
                    DungeonResponse used = controller.tick(item.getId(), Direction.NONE);
                    assertTrue(used.getInventory().stream().noneMatch(i -> i.getType() == "invisibility_potion"));
                }
            }
        });
    }

    @Test
    public void testTickInvincibilityPotion() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("InterfaceTest4", "standard");
        controller.tick(null, Direction.DOWN);
        DungeonResponse world = controller.tick(null, Direction.RIGHT);
        assertTrue(world.getInventory().stream().anyMatch(i -> i.getType() == "invincibility_potion"));
        assertDoesNotThrow(() -> {
            for (ItemResponse item : world.getInventory()) {
                if (item.getType() == "invincibility_potion") {
                    DungeonResponse used = controller.tick(item.getId(), Direction.NONE);
                    assertTrue(used.getInventory().stream().noneMatch(i -> i.getType() == "invincibility_potion"));
                }
            }
        });

    }

    @Test
    public void testUseHealthPotion() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("potionTest", "standard");
        controller.tick(null, Direction.DOWN);
        controller.tick(null, Direction.DOWN);
        DungeonResponse world = controller.tick(null, Direction.DOWN);
        assertTrue(world.getInventory().stream().anyMatch(i -> i.getType() == "health_potion"));
        // assume mercenery can hurt but cannot defeat player
        assertTrue(controller.getCurrentMap().getPlayer().getVita() < controller.getCurrentMap().getPlayer()
                .getInitialVita());
        for (ItemResponse item : world.getInventory()) {
            if (item.getType() == "health_potion") {
                assertDoesNotThrow(() -> {
                    DungeonResponse used = controller.tick(item.getId(), null);
                    assertTrue(used.getInventory().stream().noneMatch(i -> i.getType() == "health_potion"));
                });
            }
        }
        assertTrue(controller.getCurrentMap().getPlayer().getVita() == controller.getCurrentMap().getPlayer()
                .getInitialVita());
    }

    @Test
    public void testTickSpiderMovement() {
        DungeonManiaController controller = new DungeonManiaController();

        DungeonResponse world = controller.newGame("InterfaceTest2", "peaceful");
        // Check spider is circling around (3,3)
        EntityResponse target = null;
        for (EntityResponse e : world.getEntities()) {
            if (e.getType().equals("spider") && e.getPosition().getX() == 3 && e.getPosition().getY() == 3) {
                target = e;
                break;
            }
        }
        assertTrue(target.getPosition().getX() == 3 && target.getPosition().getX() == 3);
        controller.tick(null, Direction.LEFT);

    }

    @Test
    public void testTickZombieMovement() {
        DungeonManiaController controller = new DungeonManiaController();

        controller.newGame("InterfaceTest3", "peaceful");
        DungeonResponse world = controller.tick(null, Direction.NONE);
        // Make sure zombie moved
        Position pos = new Position(2, 2);
        assertTrue(world.getEntities().stream()
                .anyMatch(e -> e.getType() == "zombie_toast" && !e.getPosition().equals(pos)));
    }

    @Test
    public void testTickMercenaryMovement() {
        DungeonManiaController controller = new DungeonManiaController();

        controller.newGame("InterfaceTest2", "peaceful");
        DungeonResponse world = controller.tick(null, Direction.NONE);
        // Make sure mercenary is closer to player
        Position pos = new Position(1, 3);
        assertTrue(world.getEntities().stream()
                .anyMatch(e -> e.getType().equals("mercenary") && e.getPosition().equals(pos)));
    }

    @Test
    public void testTickInvalidArgument() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("InterfaceTest1", "standard");
        assertThrows(IllegalArgumentException.class, () -> {
            controller.tick("spider", null);
        });
    }

    @Test
    public void testTickNoSuchItem() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("InterfaceTest1", "standard");
        assertThrows(InvalidActionException.class, () -> {
            controller.tick("invincibility_potion (4 , 1)", Direction.NONE);
        });
    }

    // Tests for build()
    @Test
    public void testBuildBow() {
        DungeonManiaController controller = new DungeonManiaController();
        // Collect materials
        controller.newGame("InterfaceTest1", "standard");
        controller.tick(null, Direction.DOWN);
        controller.tick(null, Direction.DOWN);
        controller.tick(null, Direction.RIGHT);
        controller.tick(null, Direction.RIGHT);
        controller.tick(null, Direction.UP);
        // Build a bow
        assertDoesNotThrow(() -> {
            DungeonResponse world = controller.build("bow");
            assertTrue(world.getInventory().stream().anyMatch(item -> item.getType() == "bow"));
        });
    }

    @Test
    public void testBuildShieldWithTreasure() {
        DungeonManiaController controller = new DungeonManiaController();
        // Collect materials
        controller.newGame("InterfaceTest1", "standard");

        controller.tick(null, Direction.RIGHT);
        controller.tick(null, Direction.RIGHT);
        controller.tick(null, Direction.DOWN);
        controller.tick(null, Direction.LEFT);
        controller.tick(null, Direction.LEFT);
        // Build a shield
        assertDoesNotThrow(() -> {
            DungeonResponse world = controller.build("shield");
            assertTrue(world.getInventory().stream().anyMatch(item -> item.getType() == "shield"));
        });

    }

    @Test
    public void testBuildShieldWithKey() {
        DungeonManiaController controller = new DungeonManiaController();
        // Collect materials
        controller.newGame("InterfaceTest1", "standard");

        controller.tick(null, Direction.RIGHT);
        controller.tick(null, Direction.RIGHT);
        controller.tick(null, Direction.LEFT);
        controller.tick(null, Direction.LEFT);
        controller.tick(null, Direction.DOWN);
        controller.tick(null, Direction.DOWN);
        controller.tick(null, Direction.RIGHT);
        // Build a shield
        assertDoesNotThrow(() -> {
            DungeonResponse world = controller.build("shield");
            assertTrue(world.getInventory().stream().anyMatch(item -> item.getType() == "shield"));
        });

    }

    @Test
    public void testBuildNoMatierial() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("InterfaceTest1", "standard");
        assertThrows(InvalidActionException.class, () -> {
            controller.build("bow");
        });
    }

    // Tests for interact()
    @Test
    public void testInteractMercenarywithoutanyTreasure() {
        DungeonManiaController controller = new DungeonManiaController();
        DungeonResponse world = controller.newGame("InterfaceTest2", "peaceful");
        assertThrows(InvalidActionException.class, () -> {
            for (EntityResponse e : world.getEntities()) {
                if (e.getType() == "mercenary") {
                    controller.interact(e.getId());
                }
            }
        });
    }

    @Test
    public void testInteractSpawner() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("InterfaceTest2", "peaceful");
        // Pick up sword
        DungeonResponse world = controller.tick(null, Direction.RIGHT);
        for (EntityResponse e : world.getEntities()) {
            if (e.getType() == "zombie_toast_spawner") {
                controller.interact(e.getId());
            }
        }
        world = controller.tick(null, Direction.NONE);
        // Check the toast spawner is destroyed
        for (EntityResponse e : world.getEntities()) {
            if (e.getType() == "zombie_toast_spawner") {
                assertFalse(e.isInteractable());

            }
        }
    }

    @Test
    public void testInteractMercenary() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("InterfaceTest2", "standard");
        // Pick up treasure
        DungeonResponse world = controller.tick(null, Direction.DOWN);
        for (EntityResponse e : world.getEntities()) {
            if (e.getType() == "mercenary") {
                controller.interact(e.getId());
            }
        }
        controller.tick(null, Direction.DOWN);
        world = controller.tick(null, Direction.LEFT);
        assertTrue(world.getEntities().stream().anyMatch(e -> e.getType() == "mercenary"));
        assertTrue(world.getEntities().stream().anyMatch(e -> e.getType() == "player"));
    }

    @Test
    public void testInteractAssasin() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("assassinTest", "standard");
        controller.tick(null, Direction.RIGHT);
        DungeonResponse world = controller.tick(null, Direction.RIGHT);
        for (EntityResponse e : world.getEntities()) {
            if (e.getType() == "assassin") {
                controller.interact(e.getId());
            }
        }
        controller.tick(null, Direction.NONE);
        world = controller.tick(null, Direction.NONE);
        assertTrue(world.getEntities().stream().anyMatch(e -> e.getType() == "assassin"));
        assertTrue(world.getEntities().stream().anyMatch(e -> e.getType() == "player"));
    }

    @Test
    public void testInteractInvalidArgument() {
        DungeonManiaController controller = new DungeonManiaController();
        controller.newGame("InterfaceTest1", "standard");
        assertThrows(IllegalArgumentException.class, () -> {
            controller.interact("entityId");
        });
    }

    @Test
    public void testInteractMercenaryFar() {
        DungeonManiaController controller = new DungeonManiaController();
        DungeonResponse world = controller.newGame("advanced", "standard");
        assertThrows(InvalidActionException.class, () -> {
            for (EntityResponse e : world.getEntities()) {
                if (e.getType() == "mercenary") {
                    controller.interact(e.getId());
                }
            }
        });
    }

    @Test
    public void testInteractSpawnerFar() {
        DungeonManiaController controller = new DungeonManiaController();
        DungeonResponse world = controller.newGame("InterfaceTest2", "standard");
        assertThrows(InvalidActionException.class, () -> {
            for (EntityResponse e : world.getEntities()) {
                if (e.getType() == "zombie_toast_spawner") {
                    controller.interact(e.getId());
                }
            }
        });
    }

}
