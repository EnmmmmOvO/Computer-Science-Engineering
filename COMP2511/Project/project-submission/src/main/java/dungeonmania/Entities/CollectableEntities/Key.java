package dungeonmania.Entities.CollectableEntities;

import dungeonmania.MapGenerator.MapGenerator;

public class Key extends CollectableEntities {
    private int keyType;

    public int getKeyType() {
        return keyType;
    }

    public void setKeyType(int keyType) {
        this.keyType = keyType;
    }

    public Key(int x, int y) {
        super(x, y, 0, "key");
    }

    @Override
    public void interact(MapGenerator mapGenerator) {
        return;
    }

}
