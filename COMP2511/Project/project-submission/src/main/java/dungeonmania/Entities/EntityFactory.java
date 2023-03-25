package dungeonmania.Entities;

import dungeonmania.Entities.CharacterEntities.CharacterEntities;
import dungeonmania.Entities.CollectableEntities.*;
import dungeonmania.Entities.MovingEntities.*;
import dungeonmania.Entities.RareCollectableEntities.*;
import dungeonmania.Entities.StaticEntities.*;

public class EntityFactory {

    public static Entity newEntity(String type, int x, int y, String portalColour) {
        Entity entity = null;

        if ("wall".equals(type)) {
            entity = new Wall(x, y);
        } else if (type.equals("arrow")) {
            entity = new Arrows(x, y);
        } else if (type.equals("bomb")) {
            entity = new Bomb(x, y);
        } else if (type.equals("health_potion")) {
            entity = new HealthPotion(x, y);
        } else if (type.equals("invincibility_potion")) {
            entity = new InvincibilityPotion(x, y);
        } else if (type.equals("invisibility_potion")) {
            entity = new InvisibilityPotion(x, y);
        } else if (type.equals("key")) {
            entity = new Key(x, y);
        } else if (type.equals("sword")) {
            entity = new Sword(x, y);
        } else if (type.equals("armour")) {
            entity = new Armour(x, y);
        } else if (type.equals("treasure")) {
            entity = new Treasure(x, y);
        } else if (type.equals("wood")) {
            entity = new Wood(x, y);
        } else if (type.equals("mercenary")) {
            entity = new Mercenary(x, y);
        } else if (type.equals("assassin")) {
            entity = new Assassin(x, y);
        } else if (type.equals("spider")) {
            entity = new Spider(x, y);
        } else if (type.equals("zombie_toast")) {
            entity = new ZombieToast(x, y);
        } else if (type.equals("the_one_ring")) {
            entity = new TheOneRing(x, y);
        } else if (type.equals("boulder")) {
            entity = new Boulder(x, y);
        } else if (type.equals("door")) {
            entity = new Door(x, y);
        } else if (type.equals("exit")) {
            entity = new Exit(x, y);
        } else if (type.equals("switch")) {
            entity = new FloorSwitch(x, y);
        } else if (type.equals("portal")) {
            entity = new Portal(x, y, portalColour);
        } else if (type.equals("zombie_toast_spawner")) {
            entity = new ZombieToastSpawner(x, y);
        } else if (type.equals("player")) {
            entity = new CharacterEntities(x, y, 2);
        } else if (type.equals("bow")) {
            entity = new Bow(x, y);
        } else if (type.equals("shield")) {
            entity = new Shield(x, y);
        } else if (type.equals("sun_stone")) {
            entity = new SunStone(x, y);
        } else if (type.equals("sceptre")) {
            entity = new Sceptre(x, y);
        } else if (type.equals("midnight_armour")) {
            entity = new MidnightArmour(x, y);
        } else if (type.equals("hydra")) {
            entity = new Hydra(x, y);
        } else if (type.equals("anduril")) {
            entity = new Anduril(x, y);
        }
        return entity;
    }

}