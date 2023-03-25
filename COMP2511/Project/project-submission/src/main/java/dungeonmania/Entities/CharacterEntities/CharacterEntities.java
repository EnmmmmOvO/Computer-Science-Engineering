package dungeonmania.Entities.CharacterEntities;

import java.util.List;
import java.util.Random;

import dungeonmania.Battle;
import dungeonmania.Entities.Entity;
import dungeonmania.Entities.CollectableEntities.Key;
import dungeonmania.Entities.CollectableEntities.SunStone;
import dungeonmania.Entities.MovingEntities.Assassin;
import dungeonmania.Entities.MovingEntities.Hydra;
import dungeonmania.Entities.MovingEntities.Mercenary;
import dungeonmania.Entities.RareCollectableEntities.Anduril;
import dungeonmania.Entities.StaticEntities.Door;
import dungeonmania.MapGenerator.MapGenerator;
import dungeonmania.util.Direction;
import dungeonmania.util.Position;

public class CharacterEntities implements Entity, Battle {

    private Position position;
    private String Entityid;
    private final Boolean obstacle = false;
    private final Boolean isInteractable = false;
    private final Double initialAttack = 100.0;
    private final Double initialVita = 100.0;
    private Double attack;
    private Double vita;
    private Boolean isInvinceble = false;
    private Boolean isInvisible = false;

    public CharacterEntities(int x, int y, int layer) {
        this.position = new Position(x, y, layer);
        this.Entityid = "player (" + x + " , " + y + ")";
        this.attack = initialAttack;
        this.vita = initialVita;
    }

    public Double getVita() {
        return vita;
    }

    public Double getAttack() {
        return attack;
    }

    public void setVita(Double vita) {
        this.vita = vita;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        CharacterEntities other = (CharacterEntities) obj;

        return position == other.position;
    }

    public void move(Direction direction) {
        this.setPosition(this.getPosition().translateBy(direction));
    }

    @Override
    public void update(MapGenerator mapGenerator, Direction direction) {
        if (this.vita <= 0.0) {
            mapGenerator.removeEntity(this);
            return;
        }
        if (direction == null) {
            return;
        }

        List<Entity> elist = mapGenerator.getEntities();
        Entity player = null;
        for (Entity e : elist) {
            if (e.equals(this)) {
                player = e;
            }
        }

        Key key = mapGenerator.getKey();
        SunStone sunStone = mapGenerator.getSunStone();
        for (Entity e : elist) {
            Position destination = player.getPosition().translateBy(direction);
            if (e.getPosition().equals(destination)) {

                if (e instanceof Door && key != null) {
                    Door door = (Door) e;
                    if (key.getKeyType() == door.getKeyType()) {
                        door.setObstacle(false);
                        door.setType("door-open");
                        mapGenerator.removeKey(key);
                    }
                } else if (e instanceof Door && sunStone != null) {
                    Door door = (Door) e;
                    door.setObstacle(false);
                    door.setType("door-open");
                }
                if (e.isObstacle()) {
                    return;
                }
            }
        }
        player.move(direction);
    }

    @Override
    public void interact(MapGenerator mapGenerator) {
        return;
    }

    @Override
    public void battle(MapGenerator mapGenerator, Battle enemy) {
        if (enemy.equals(this))
            return;
        if (enemy instanceof Mercenary && ((Mercenary) enemy).isAlly())
            return;

        if (enemy instanceof Assassin) {
            if (((Assassin) enemy).isAlly()) {
                return;
            }
        }
        if (this.isInvinceble) {
            enemy.setVita(-1.0);
        }
        Random random = new Random();
        int nextInt = random.nextInt(1000);
        if (enemy instanceof Hydra && nextInt > 500
                && mapGenerator.getInventoryList().stream().noneMatch(ele -> ele instanceof Anduril)) {
            if (enemy.getVita() + ((this.getVita() * this.getAttack()) / 5) > 10) {
                enemy.setVita(10.0);
            } else {
                enemy.setVita((enemy.getVita() + ((this.getVita() * this.getAttack()) / 5)));
            }
            return;
        } else {
            if (mapGenerator.getInventoryList().stream().anyMatch(ele -> ele instanceof Anduril)
                    && (enemy instanceof Assassin || enemy instanceof Hydra)) {
                enemy.setVita((enemy.getVita() - ((this.getVita() * this.getAttack()) / 5 * 3)));
            } else {
                enemy.setVita((enemy.getVita() - ((this.getVita() * this.getAttack()) / 5)));
            }

        }

        if (enemy.getVita() <= 0.0) {
            mapGenerator.removeEntity((Entity) enemy);
            mapGenerator.removeEnemyList((Entity) enemy);
        }
    }

    public String getType() {
        return "player";
    }

    public String getId() {
        return Entityid;
    }

    public Position getPosition() {
        return position;
    }

    public int getPositionX() {
        return getPosition().getX();
    }

    public int getPositionY() {
        return getPosition().getY();
    }

    public int getPositionLayer() {
        return getPosition().getLayer();
    }

    public Boolean getIsInvinceble() {
        return isInvinceble;
    }

    public Boolean getIsInvisible() {
        return isInvisible;
    }

    public Double getInitialVita() {
        return initialVita;
    }

    public Double getInitialAttack() {
        return initialAttack;
    }

    public void setIsInvinceble(Boolean invincibility) {
        this.isInvinceble = invincibility;
    }

    public void setIsInvisible(Boolean invisibility) {
        this.isInvisible = invisibility;
    }

    public void setPosition(int x, int y, int layer) {
        this.position = new Position(x, y, layer);
    }

    public void setPosition(Position newPosition) {
        this.position = newPosition;
    }

    public Boolean isObstacle() {
        return obstacle;
    }

    public Boolean isInteractable() {
        return isInteractable;
    }

}