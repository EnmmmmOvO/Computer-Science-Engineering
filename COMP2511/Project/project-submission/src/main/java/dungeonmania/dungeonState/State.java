package dungeonmania.dungeonState;

import dungeonmania.Battle;
import dungeonmania.MapGenerator.MapGenerator;

public interface State {

    public void determin(MapGenerator map, Battle one, Battle two);

}
