package dungeonmania.dungeonState;

import dungeonmania.Battle;
import dungeonmania.MapGenerator.MapGenerator;

public class StandardState implements State {

    @Override
    public void determin(MapGenerator map, Battle one, Battle two) {
        map.addBattleList(one);
        map.addBattleList(two);
    }

}
