package dungeonmania.Entities.CollectableEntities;

import dungeonmania.MapGenerator.MapGenerator;

public class SunStone extends CollectableEntities {
    
    public SunStone(int x, int y) {
        super(x, y, 0, "sun_stone");
    }

    @Override
    public void interact(MapGenerator mapGenerator) {
        return;

    }

}
