package dungeonmania.MapGenerator;

import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.time.LocalDateTime;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonIOException;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import com.google.gson.JsonSyntaxException;

import dungeonmania.Battle;
import dungeonmania.DungeonManiaController;
import dungeonmania.Entities.Entity;
import dungeonmania.Entities.EntityFactory;
import dungeonmania.Entities.CharacterEntities.CharacterEntities;
import dungeonmania.Entities.CollectableEntities.Armour;
import dungeonmania.Entities.CollectableEntities.Arrows;
import dungeonmania.Entities.CollectableEntities.Bomb;
import dungeonmania.Entities.CollectableEntities.BuildableFactory;
import dungeonmania.Entities.CollectableEntities.CollectableEntities;
import dungeonmania.Entities.CollectableEntities.HealthPotion;
import dungeonmania.Entities.CollectableEntities.InvincibilityPotion;
import dungeonmania.Entities.CollectableEntities.InvisibilityPotion;
import dungeonmania.Entities.CollectableEntities.Key;
import dungeonmania.Entities.CollectableEntities.SunStone;
import dungeonmania.Entities.CollectableEntities.Treasure;
import dungeonmania.Entities.CollectableEntities.Wood;
import dungeonmania.Entities.MovingEntities.Assassin;
import dungeonmania.Entities.MovingEntities.Hydra;
import dungeonmania.Entities.MovingEntities.Mercenary;
import dungeonmania.Entities.MovingEntities.MovingEntities;
import dungeonmania.Entities.MovingEntities.ZombieToast;
import dungeonmania.Entities.StaticEntities.Door;
import dungeonmania.Entities.StaticEntities.PlacedBomb;
import dungeonmania.Entities.StaticEntities.ZombieToastSpawner;
import dungeonmania.Goals.Goal;
import dungeonmania.Goals.GoalComposite;
import dungeonmania.Goals.LeafFactory;
import dungeonmania.dungeonState.HardState;
import dungeonmania.dungeonState.PeacefulState;
import dungeonmania.dungeonState.StandardState;
import dungeonmania.dungeonState.State;
import dungeonmania.exceptions.InvalidActionException;
import dungeonmania.response.models.DungeonResponse;
import dungeonmania.response.models.EntityResponse;
import dungeonmania.response.models.ItemResponse;
import dungeonmania.util.Direction;
import dungeonmania.util.FileLoader;
import dungeonmania.util.Position;

public class MapGenerator {

    private List<Entity> entityList = new ArrayList<>();
    private List<Entity> inventoryList = new ArrayList<>();
    private List<Entity> enemyList = new ArrayList<>();
    private List<Battle> battleList = new ArrayList<>();
    private Set<String> buildableSet = new HashSet<>();
    private int spawnedSpider = 0;
    private String gameMode;
    private String dungeonName;
    private String dungeonid;
    private String goalStr;
    private int width;
    private int height;
    private Goal goal;
    private CharacterEntities player;
    private int tickTimes = 0;

    private State state;
    private State peaceful;
    private State standard;
    private State hard;

    public MapGenerator(String dungeonName, String gameMode) {

        this.gameMode = gameMode;
        this.dungeonName = dungeonName;
        this.dungeonid = dungeonName + "-" + LocalDateTime.now().toString();
        String filename = "src/main/resources/dungeons/" + dungeonName + ".json";

        this.peaceful = new PeacefulState();
        this.standard = new StandardState();
        this.hard = new HardState();

        if (this.gameMode.equals("peaceful")) {
            this.state = this.peaceful;
        } else if (this.gameMode.equals("standard")) {
            this.state = this.standard;
        } else if (this.gameMode.equals("hard")) {
            this.state = this.hard;
        }

        try {

            JsonObject obj = JsonParser.parseReader(new FileReader(filename)).getAsJsonObject();
            JsonArray entities = obj.getAsJsonArray("entities");

            this.width = Integer.parseInt(obj.get("width").toString());
            this.height = Integer.parseInt(obj.get("height").toString());

            for (JsonElement entity : entities) {

                String tp = entity.getAsJsonObject().get("type").toString();
                String colour = entity.getAsJsonObject().get("colour") != null
                        ? entity.getAsJsonObject().get("colour").toString()
                        : null;
                Entity newEntity = EntityFactory.newEntity(tp.substring(1, tp.length() - 1),
                        Integer.parseInt(entity.getAsJsonObject().get("x").toString()),
                        Integer.parseInt(entity.getAsJsonObject().get("y").toString()), colour);
                entityList.add(newEntity);

                if (newEntity instanceof MovingEntities) {
                    enemyList.add(newEntity);
                }

                if (newEntity instanceof CharacterEntities) {
                    this.player = (CharacterEntities) newEntity;
                }

                if (newEntity instanceof Door) {
                    Door door = (Door) newEntity;
                    door.setKeyType(Integer.parseInt(entity.getAsJsonObject().get("key").toString()));
                }

                if (newEntity instanceof Key) {
                    Key key = (Key) newEntity;
                    key.setKeyType(Integer.parseInt(entity.getAsJsonObject().get("key").toString()));
                }

            }

            JsonObject goals = obj.getAsJsonObject("goal-condition");

            if (isLeaf(goals)) {

                String tmpgoal = goals.get("goal").toString();
                this.goal = LeafFactory.newLeaf(tmpgoal.substring(1, tmpgoal.length() - 1), this);

            } else {

                this.goal = new GoalComposite(this, goals);

            }

            this.goalStr = goal.toString();

        } catch (JsonIOException e) {
            e.printStackTrace();
        } catch (JsonSyntaxException e) {
            e.printStackTrace();
        } catch (FileNotFoundException e) {
            e.printStackTrace();
        }

    }

    public DungeonResponse newGame(String dungeonName, String gameMode, DungeonManiaController controller)
            throws IllegalArgumentException {

        if (!controller.gameModeContains(gameMode)) {
            throw new IllegalArgumentException("not a exist game mode");
        }

        String path = "dungeons";

        try {

            if (!FileLoader.listFileNamesInResourceDirectory(path).contains(dungeonName)) {
                throw new IllegalArgumentException("not a exist dungeon Name");
            }

        } catch (IOException e1) {
            e1.printStackTrace();
        }

        List<EntityResponse> entities = new ArrayList<>();
        MapGenerator map = new MapGenerator(dungeonName, gameMode);
        List<Entity> entityList = map.getEntities();

        controller.setCurrentMap(map);

        for (Entity e : entityList) {
            entities.add(newEntityResponse(e));
        }

        return newMapResponse(controller, entities, new ArrayList<>(), new ArrayList<>());

    }

    public DungeonResponse saveGame(String name, DungeonManiaController controller) throws IllegalArgumentException {

        if (controller.getCurrentMap() == null) {
            throw new IllegalArgumentException("not a exist dungeon ID");
        }

        controller.putMaps(name, this);

        List<Entity> entityList = controller.currentEntities();
        List<EntityResponse> entities = new ArrayList<>();

        for (Entity e : entityList) {
            entities.add(newEntityResponse(e));
        }

        List<ItemResponse> newItems = new ArrayList<>();
        List<Entity> itemlist = controller.currentInventoryList();

        for (Entity e : itemlist) {
            newItems.add(new ItemResponse(e.getId(), e.getType()));
        }

        return newMapResponse(controller, entities, new ArrayList<>(), new ArrayList<>());

    }

    public DungeonResponse loadGame(String name, DungeonManiaController controller) throws IllegalArgumentException {

        if (controller.getCurrentMap() == null) {
            throw new IllegalArgumentException("not a exist dungeon ID");
        } else if (!controller.getMaps().containsKey(name)) {
            throw new IllegalArgumentException("not a exist dungeon ID");
        }

        controller.setCurrentMap(controller.getMaps().get(name));

        List<Entity> entityList = controller.currentEntities();
        List<EntityResponse> entities = new ArrayList<>();

        for (Entity e : entityList) {
            entities.add(newEntityResponse(e));
        }

        List<ItemResponse> newItems = new ArrayList<>();
        List<Entity> itemlist = controller.currentInventoryList();

        for (Entity e : itemlist) {
            newItems.add(new ItemResponse(e.getId(), e.getType()));
        }

        return newMapResponse(controller, entities, newItems, controller.currentBuildableList());

    }

    public DungeonResponse tick(String itemUsed, Direction movementDirection, DungeonManiaController controller)
            throws IllegalArgumentException, InvalidActionException {

        if (itemUsed != null) {

            for (Entity e : controller.currentInventoryList()) {

                if (e.getId().equals(itemUsed) && !(e instanceof Bomb || e instanceof HealthPotion
                        || e instanceof InvincibilityPotion || e instanceof InvisibilityPotion)) {

                    throw new IllegalArgumentException("not a allowed inventory");

                }

            }

            if (controller.currentEntities().stream().filter(e -> e.getId().equals(itemUsed))
                    .filter(e -> e instanceof CollectableEntities) == null) {

                throw new IllegalArgumentException("not a allowed inventory");

            }

            if (controller.currentEntities().stream().noneMatch(e -> e.getId().equals(itemUsed))
                    && controller.currentInventoryList().stream().noneMatch(e -> e.getId().equals(itemUsed))) {

                throw new IllegalArgumentException("not a allowed inventory");

            }

            if (!controller.currentInventoryList().stream().anyMatch(i -> i.getId().equals(itemUsed))) {

                throw new InvalidActionException("item not in the inventory");

            }

            for (Entity e : controller.currentInventoryList()) {

                if (e.getId().equals(itemUsed)) {

                    if (e instanceof HealthPotion) {
                        this.player.setVita(this.player.getInitialVita());
                    }

                    if (e instanceof InvincibilityPotion) {
                        this.player.setIsInvinceble(true);
                    }

                    if (e instanceof InvisibilityPotion) {
                        this.player.setIsInvisible(true);
                    }

                    if (e instanceof Bomb) {
                        PlacedBomb bombPlaced = new PlacedBomb(player.getPosition().getX(),
                                player.getPosition().getY());
                        entityList.add(bombPlaced);
                    }

                }

            }

            // waiting for appending useitem status
            List<Entity> rmInventory = new ArrayList<>();

            controller.currentInventoryList().stream().filter(e -> e.getId().equals(itemUsed))
                    .forEach(e -> rmInventory.add(e));

            rmInventory.forEach(e -> controller.getCurrentMap().removeInventoryList(e));

        }

        _spawnSpider();
        _spawnMercenary();
        _spawnAssassin();
        if (gameMode.equals("hard")) {
            _spawnHydra();
        }

        this.tickTimes++;

        controller.getCurrentMap().update(itemUsed, movementDirection);

        List<EntityResponse> newEntities = new ArrayList<>();
        List<Entity> entityList = controller.currentEntities();

        for (Entity e : entityList) {
            newEntities.add(newEntityResponse(e));
        }

        List<ItemResponse> newItems = new ArrayList<>();
        List<Entity> itemlist = controller.currentInventoryList();

        for (Entity e : itemlist) {
            newItems.add(new ItemResponse(e.getId(), e.getType()));
        }

        return newMapResponse(controller, newEntities, newItems, controller.currentBuildableList());

    }

    private void _spawnSpider() {
        if (this.tickTimes % 10 == 0 && spawnedSpider < 8) {
            Random random = new Random();
            int x = random.nextInt(this.width - 3);
            int y = random.nextInt(this.height - 3);
            Entity spider = EntityFactory.newEntity("spider", x, y, "Default");
            this.entityList.add(spider);
            this.enemyList.add(spider);
            spawnedSpider++;
        }
    }

    private void _spawnHydra() {
        if (this.tickTimes > 2 && this.tickTimes % 50 == 0) {
            Random random = new Random();
            int x = random.nextInt(this.width - 3);
            int y = random.nextInt(this.height - 3);
            if (x < 3)
                x += 3;
            if (y < 3)
                x += 3;
            Entity hydra = new Hydra(x, y);
            this.entityList.add(hydra);
            this.enemyList.add(hydra);
        }
    }

    private void _spawnMercenary() {
        if (this.tickTimes % 11 == 0 && this.tickTimes > 2) {
            Entity mercenary = new Mercenary(1, 1);
            this.entityList.add(mercenary);
            this.enemyList.add(mercenary);
        }
    }

    private void _spawnAssassin() {
        if (this.tickTimes % 30 == 0 && this.tickTimes > 2) {
            Entity assassin = new Assassin(1, 1);
            this.entityList.add(assassin);
            this.enemyList.add(assassin);
        }
    }

    public DungeonResponse build(String buildable, DungeonManiaController controller)
            throws IllegalArgumentException, InvalidActionException {

        controller.getCurrentMap().buildInventory(buildable);

        List<EntityResponse> newEntities = new ArrayList<>();
        List<Entity> entityList = controller.currentEntities();

        for (Entity e : entityList) {
            newEntities.add(newEntityResponse(e));
        }

        List<ItemResponse> newItems = new ArrayList<>();
        List<Entity> itemlist = controller.currentInventoryList();

        for (Entity e : itemlist) {
            newItems.add(new ItemResponse(e.getId(), e.getType()));
        }

        return newMapResponse(controller, newEntities, newItems, controller.currentBuildableList());

    }

    public void update(String itemUsed, Direction movementDirection) {

        notifyEntity(movementDirection);

        List<Battle> tmpBattleList = new ArrayList<Battle>(battleList);
        for (Battle e : tmpBattleList) {
            for (Battle ee : tmpBattleList) {
                e.battle(this, ee);
            }
        }

        player.update(this, movementDirection);
        battleList.clear();
        this.updateGoal();

        List<Entity> woodList = new ArrayList<>();
        List<Entity> arrowList = new ArrayList<>();
        List<Entity> treasureList = new ArrayList<>();
        List<Entity> keyList = new ArrayList<>();
        List<Entity> sunStoneList = new ArrayList<>();
        List<Entity> armourList = new ArrayList<>();

        inventoryList.stream().filter(i -> i instanceof Wood).forEach(w -> woodList.add(w));
        inventoryList.stream().filter(i -> i instanceof Arrows).forEach(w -> arrowList.add(w));
        inventoryList.stream().filter(i -> i instanceof Treasure).forEach(w -> treasureList.add(w));
        inventoryList.stream().filter(i -> i instanceof Key).forEach(w -> keyList.add(w));
        inventoryList.stream().filter(i -> i instanceof SunStone).forEach(w -> sunStoneList.add(w));
        inventoryList.stream().filter(i -> i instanceof Armour).forEach(w -> armourList.add(w));

        if (woodList.size() >= 1 && (arrowList.size() >= 3)) {
            buildableSet.add("bow");
        }
        if (woodList.size() >= 2 && (treasureList.size() >= 1 || keyList.size() >= 1 || sunStoneList.size() >= 1)) {
            buildableSet.add("shield");
        }
        if ((woodList.size() >= 1 || arrowList.size() >= 2) && (treasureList.size() >= 1 || keyList.size() >= 1)
                && sunStoneList.size() >= 1) {
            buildableSet.add("sceptre");
        }
        if (armourList.size() >= 1 && sunStoneList.size() >= 1) {

            buildableSet.add("midnight_armour");
            if (enemyList.stream().anyMatch(e -> e instanceof ZombieToast)) {
                buildableSet.remove("midnight_armour");
            }
        }

    }

    public DungeonResponse interact(String entityId, DungeonManiaController controller)
            throws IllegalArgumentException, InvalidActionException {

        Entity target = null;
        List<Entity> entityList = controller.currentEntities();

        for (Entity e : entityList) {
            if (e.getId().equals(entityId)) {
                target = e;
            }
        }

        if (target == null) {
            throw new IllegalArgumentException("not a valid entity ID");
        }

        if (target instanceof Mercenary || target instanceof Assassin) {

            if (player.getPositionX() == target.getPositionX()) {
                if (Math.abs(player.getPositionY() - target.getPositionY()) > 2) {
                    throw new InvalidActionException("too far to interact");
                }
            }

            if (player.getPositionY() == target.getPositionY()) {
                if (Math.abs(player.getPositionX() - target.getPositionX()) > 2) {
                    throw new InvalidActionException("too far to interact");
                }
            }

            if (player.getPositionY() != target.getPositionY() && player.getPositionX() != target.getPositionX()) {

                int x = player.getPositionX() - target.getPositionX();
                int y = player.getPositionY() - target.getPositionY();

                if (x - y != 0) {
                    throw new InvalidActionException("too far to interact");
                }

            }

        } else if (target instanceof ZombieToastSpawner) {

            if (!Position.isAdjacent(player.getPosition(), target.getPosition())) {
                throw new InvalidActionException("too far to interact");
            }

        }

        target.interact(this);

        List<EntityResponse> newEntities = new ArrayList<>();
        List<Entity> updatedentityList = controller.currentEntities();

        for (Entity e : updatedentityList) {
            newEntities.add(newEntityResponse(e));
        }

        List<ItemResponse> newItems = new ArrayList<>();
        List<Entity> itemlist = controller.currentInventoryList();

        for (Entity e : itemlist) {
            newItems.add(new ItemResponse(e.getId(), e.getType()));
        }

        return newMapResponse(controller, newEntities, newItems, controller.currentBuildableList());

    }

    public void notifyEntity(Direction direction) {

        List<Entity> tempEntityList = new ArrayList<Entity>(entityList);

        for (Entity e : tempEntityList) {
            if (!(e instanceof CharacterEntities)) {
                e.update(this, direction);
            }
        }

    }

    public void buildInventory(String buildable) {
        if (buildableSet.contains(buildable)) {
            BuildableFactory.build(this, buildable);
        } else {
            throw new InvalidActionException("insufficient items");
        }
    }

    public void updateGoal() {
        this.goalStr = goal.toString();
        if (this.goal.pass()) {
            this.goalStr = "";
        }
    }

    public boolean isLeaf(JsonObject obj) {
        return obj.has("subgoals") == false;
    }

    public EntityResponse newEntityResponse(Entity e) {
        Position newPosition = new Position(e.getPositionX(), e.getPositionY(), e.getPositionLayer());
        EntityResponse newEntity = new EntityResponse(e.getId(), e.getType(), newPosition, e.isInteractable());
        return newEntity;
    }

    public DungeonResponse newMapResponse(DungeonManiaController controller, List<EntityResponse> entities,
            List<ItemResponse> items, List<String> buildable) {

        DungeonResponse newResponse = new DungeonResponse(controller.currentDungeonId(), dungeonName, entities, items,
                buildable, controller.currentGoalStr());

        return newResponse;

    }

    public Position playerPosition() {
        return getPlayer().getPosition();
    }

    public boolean playerIsInvisible() {
        return getPlayer().getIsInvisible();
    }

    public boolean playerIsInviceble() {
        return getPlayer().getIsInvinceble();
    }

    public void addInventoryList(Entity e) {
        inventoryList.add(e);
    }

    public void addBattleList(Battle e) {
        battleList.add(e);
    }

    public void removeBattleList(Battle e) {
        battleList.remove(e);
    }

    public void removeEntity(Entity e) {
        entityList.remove(e);
    }

    public void removeInventoryList(Entity e) {
        inventoryList.remove(e);
    }

    public void removeEnemyList(Entity e) {
        enemyList.remove(e);
    }

    public void removeBuildableSet(String e) {
        buildableSet.remove(e);
    }

    public void removeKey(Key key) {
        removeInventoryList(key);
    }

    public State getState() {
        return state;
    }

    public List<Battle> getBattleList() {
        return battleList;
    }

    public List<Entity> getInventoryList() {
        return inventoryList;
    }

    public List<Entity> getEntities() {
        return entityList;
    }

    public List<String> getBuildableList() {
        List<String> buildableList = new ArrayList<>(buildableSet);
        return buildableList;
    }

    public String getDungeonName() {
        return dungeonName;
    }

    public String getDungeonId() {
        return dungeonid;
    }

    public List<Entity> getEnemyList() {
        return enemyList;
    }

    public String getGoalStr() {
        return goalStr;
    }

    public CharacterEntities getPlayer() {
        return player;
    }

    public int getHeight() {
        return height;
    }

    public int getWidth() {
        return width;
    }

    public String getGameMode() {
        return gameMode;
    }

    public Key getKey() {
        for (Entity entity : this.getInventoryList()) {
            if (entity instanceof Key) {
                return (Key) entity;
            }
        }
        return null;
    }

    public SunStone getSunStone() {
        for (Entity entity : this.getInventoryList()) {
            if (entity instanceof SunStone) {
                return (SunStone) entity;
            }
        }
        return null;
    }

    public void setEntities(List<Entity> entityList) {
        this.entityList = entityList;
    }

    public void setInventoryList(List<Entity> inventoryList) {
        this.inventoryList = inventoryList;
    }

}
