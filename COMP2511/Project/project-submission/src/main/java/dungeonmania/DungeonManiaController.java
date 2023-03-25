package dungeonmania;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import dungeonmania.Entities.Entity;
import dungeonmania.MapGenerator.MapGenerator;
import dungeonmania.exceptions.InvalidActionException;
import dungeonmania.response.models.DungeonResponse;
import dungeonmania.util.Direction;
import dungeonmania.util.FileLoader;

public class DungeonManiaController {

    private Map<String, MapGenerator> maps = new HashMap<String, MapGenerator>();
    private MapGenerator currentMap = null;

    public DungeonManiaController() {
    }

    /**
     * /dungeons
     * 
     * Done for you.
     */
    public static List<String> dungeons() {
        try {
            return FileLoader.listFileNamesInResourceDirectory("/dungeons");
        } catch (IOException e) {
            return new ArrayList<>();
        }
    }

    public DungeonResponse newGame(String dungeonName, String gameMode) throws IllegalArgumentException {

        MapGenerator newMap = new MapGenerator(dungeonName, gameMode);
        DungeonResponse newResponse = newMap.newGame(dungeonName, gameMode, this);
        return newResponse;

    }

    public DungeonResponse saveGame(String name) throws IllegalArgumentException {

        DungeonResponse newResponse = this.currentMap.saveGame(name, this);
        return newResponse;

    }

    public DungeonResponse loadGame(String name) throws IllegalArgumentException {

        DungeonResponse newResponse = this.currentMap.loadGame(name, this);
        return newResponse;

    }

    public List<String> allGames() {

        return new ArrayList<>(this.maps.keySet());

    }

    public DungeonResponse tick(String itemUsed, Direction movementDirection)
            throws IllegalArgumentException, InvalidActionException {

        DungeonResponse newResponse = this.currentMap.tick(itemUsed, movementDirection, this);
        return newResponse;

    }

    public DungeonResponse interact(String entityId) throws IllegalArgumentException, InvalidActionException {

        DungeonResponse newResponse = this.currentMap.interact(entityId, this);
        return newResponse;

    }

    public DungeonResponse build(String buildable) throws IllegalArgumentException, InvalidActionException {

        DungeonResponse newResponse = this.currentMap.build(buildable, this);
        return newResponse;

    }

    public void putMaps(String key, MapGenerator value) {
        maps.put(key, value);
    }

    public MapGenerator getCurrentMap() {
        return currentMap;
    }

    public Map<String, MapGenerator> getMaps() {
        return maps;
    }

    public String getSkin() {
        return "default";
    }

    public String getLocalisation() {
        return "en_US";
    }

    public List<String> getGameModes() {
        return Arrays.asList("standard", "peaceful", "hard");
    }

    public void setCurrentMap(MapGenerator currentMap) {
        this.currentMap = currentMap;
    }

    public boolean gameModeContains(String gameMode) {
        return getGameModes().contains(gameMode);
    }

    public String currentDungeonId() {
        return getCurrentMap().getDungeonId();
    }

    public String currentDungeonName() {
        return getCurrentMap().getDungeonName();
    }

    public String currentGoalStr() {
        return getCurrentMap().getGoalStr();
    }

    public List<Entity> currentEntities() {
        return getCurrentMap().getEntities();
    }

    public List<Entity> currentInventoryList() {
        return getCurrentMap().getInventoryList();
    }

    public List<String> currentBuildableList() {
        return getCurrentMap().getBuildableList();
    }

}
