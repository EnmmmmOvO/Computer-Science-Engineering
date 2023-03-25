package dungeonmania.Entities.CollectableEntities;

import dungeonmania.MapGenerator.MapGenerator;

public class BuildableFactory {

    public static void build(MapGenerator map, String buildable) {
        if (buildable.equals("bow")) {
            Bow.build(map, buildable);
        } else if (buildable.equals("shield")) {
            Shield.build(map, buildable);
        } else if (buildable.equals("sceptre")) {
            Sceptre.build(map, buildable);
        } else if (buildable.equals("midnight_armour")) {
            MidnightArmour.build(map, buildable);
        }
    }

}
