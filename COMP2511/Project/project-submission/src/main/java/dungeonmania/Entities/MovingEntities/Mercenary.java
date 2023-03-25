package dungeonmania.Entities.MovingEntities;

import java.time.LocalDateTime;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import dungeonmania.Battle;
import dungeonmania.Entities.Entity;
import dungeonmania.Entities.CharacterEntities.CharacterEntities;
import dungeonmania.Entities.CollectableEntities.Sceptre;
import dungeonmania.Entities.CollectableEntities.SunStone;
import dungeonmania.Entities.CollectableEntities.Treasure;
import dungeonmania.MapGenerator.MapGenerator;
import dungeonmania.exceptions.InvalidActionException;
import dungeonmania.util.Direction;
import dungeonmania.util.Position;

public class Mercenary extends MovingEntities {

    private Double attack = 10.0;
    private Double vita = 10.0;
    private boolean ally = false;

    public Mercenary(int x, int y) {
        super(x, y, 2, "mercenary", "mercenary" + LocalDateTime.now().toString().replaceAll("-", ""), true);
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

    public boolean isAlly() {
        return ally;
    }

    @Override
    public void update(MapGenerator mapGenerator, Direction direction) {

        if (mapGenerator.playerIsInvisible()) {
            return;
        }

        List<Entity> elist = mapGenerator.getEntities();
        Entity enemy = null;
        Entity player = null;

        for (Entity e : elist) {
            if (e.equals(this)) {
                enemy = e;
            }
            if (e instanceof CharacterEntities) {
                player = e;
            }
        }

        if (player.getPosition().equals(enemy.getPosition())) {
            return;
        }

        Map<Position, Integer> dist = new HashMap<Position, Integer>();
        Map<Position, Boolean> vst = new HashMap<Position, Boolean>();
        Map<Position, Position> pred = new HashMap<Position, Position>();

        for (Entity e : elist) {
            dist.put(e.getPosition(), Integer.MAX_VALUE);
            pred.put(e.getPosition(), null);
        }

        for (int i = 0; i < mapGenerator.getWidth(); i++) {
            for (int j = 0; j < mapGenerator.getHeight(); j++) {
                boolean already = false;
                for (Position p : dist.keySet()) {
                    if (p.getX() == i && p.getY() == j) {
                        already = true;
                    }
                }
                if (!already) {
                    Position np = new Position(i, j);
                    dist.put(np, Integer.MAX_VALUE);
                    pred.put(np, null);
                }
            }
        }

        int numRemoved = 0;
        for (Entity e : elist) {
            if (e.isObstacle()) {
                dist.remove(e.getPosition());
                pred.remove(e.getPosition());
                numRemoved++;
            }
        }

        for (Position p : dist.keySet()) {
            vst.put(p, false);
        }

        dist.replace(enemy.getPosition(), 0);

        for (int i = 0; i < mapGenerator.getHeight() * mapGenerator.getWidth() - numRemoved; i++) {
            int min = Integer.MAX_VALUE;
            Position u = null;
            for (Position p : dist.keySet()) {
                if (dist.get(p) <= min && vst.get(p) != true) {
                    min = dist.get(p);
                    u = p;
                }
            }

            vst.replace(u, true);

            Position up = null;
            Position down = null;
            Position left = null;
            Position right = null;

            for (Position p : dist.keySet()) {
                if (u.translateBy(Direction.UP).equals(p)) {
                    up = p;
                }
                if (u.translateBy(Direction.DOWN).equals(p)) {
                    down = p;
                }
                if (u.translateBy(Direction.LEFT).equals(p)) {
                    left = p;
                }
                if (u.translateBy(Direction.RIGHT).equals(p)) {
                    right = p;
                }
            }

            if (up != null) {
                if (dist.get(u) + 1 < dist.get(up)) {
                    dist.replace(up, dist.get(u) + 1);
                    pred.replace(up, u);
                }
            }
            if (down != null) {
                if (dist.get(u) + 1 < dist.get(down)) {
                    dist.replace(down, dist.get(u) + 1);
                    pred.replace(down, u);
                }
            }
            if (left != null) {
                if (dist.get(u) + 1 < dist.get(left)) {
                    dist.replace(left, dist.get(u) + 1);
                    pred.replace(left, u);
                }
            }
            if (right != null) {
                if (dist.get(u) + 1 < dist.get(right)) {
                    dist.replace(right, dist.get(u) + 1);
                    pred.replace(right, u);
                }
            }

        }

        Position crrP = player.getPosition();
        Position preP = null;

        while (crrP != null && !crrP.equals(enemy.getPosition())) {
            preP = crrP;
            crrP = pred.get(crrP);
        }

        enemy.setPosition(preP);

        Position p = player.getPosition();

        player.update(mapGenerator, direction);
        if (player.getPosition().equals(enemy.getPosition())) {
            mapGenerator.getState().determin(mapGenerator, this, (Battle) player);
        }
        player.setPosition(p);

    }

    @Override
    public void battle(MapGenerator mapGenerator, Battle enemy) {
        if (mapGenerator.playerIsInviceble()) {
            return;
        }
        if (enemy.equals(this)) {
            return;
        }

        if (mapGenerator.playerIsInvisible()) {
            return;
        }

        if (this.isAlly()) {
            if (enemy instanceof CharacterEntities) {
                mapGenerator.removeEnemyList(this);
                return;
            }
        }

        enemy.setVita(enemy.getVita() - ((getVita() * getAttack()) / 10));

        if (enemy.getVita() <= 0.0) {
            mapGenerator.removeEntity((Entity) enemy);
            mapGenerator.removeEnemyList((Entity) enemy);
            return;
        }

    }

    @Override
    public void interact(MapGenerator curMap) {

        List<Entity> inventorys = curMap.getInventoryList();

        for (Entity e : inventorys) {
            if (e instanceof Treasure) {
                curMap.removeInventoryList(e);
                super.setIsInteractable(false);
                curMap.removeEnemyList(this);
                this.ally = true;
                return;
            } else if (e instanceof SunStone) {
                super.setIsInteractable(false);
                curMap.removeEnemyList(this);
                this.ally = true;
                return;
            } else if (e instanceof Sceptre) {
                curMap.removeInventoryList(e);
                super.setIsInteractable(false);
                curMap.removeEnemyList(this);
                this.ally = true;
                return;
            }
        }

        throw new InvalidActionException("Unsufficient item to bribe/mind-control a mercenary");

    }

}
