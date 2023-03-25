package dungeonmania.Goals;

import dungeonmania.MapGenerator.MapGenerator;

public abstract class GoalLeaf implements Goal {

    protected String type;
    protected MapGenerator map;

    public GoalLeaf(String type, MapGenerator map) {
        this.type = type;
        this.map = map;
    }

    @Override
    public abstract boolean pass();

    @Override
    public String toString() {

        if (this.pass()) {
            return "";
        } else {
            return ":" + this.type;
        }

    }

}
