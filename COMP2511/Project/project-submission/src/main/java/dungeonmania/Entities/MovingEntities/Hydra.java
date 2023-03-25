package dungeonmania.Entities.MovingEntities;

import dungeonmania.Battle;
import dungeonmania.Entities.CharacterEntities.CharacterEntities;
import dungeonmania.Entities.Entity;
import dungeonmania.Entities.StaticEntities.Wall;
import dungeonmania.MapGenerator.MapGenerator;
import dungeonmania.util.Direction;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

public class Hydra extends MovingEntities {
    private Double attack = 10.0;
    private Double vita = 10.0;

    public Hydra(int x, int y) {
        super(x, y, 2, "hydra", false);
    }

    @Override
    public Double getVita() {
        return this.vita;
    }

    @Override
    public Double getAttack() {
        return this.attack;
    }

    @Override
    public void setVita(Double vita) {
        this.vita = vita;
    }

    @Override
    public void update(MapGenerator mapGenerator, Direction direction) {
        Random random = new Random();
        int randomInt = random.nextInt(1000);
        ArrayList<Direction> directions = _obtainLegalMovement(mapGenerator.getEntities());
        this.setPosition(this.getPosition().translateBy(directions.get(randomInt % directions.size())));
        if (mapGenerator.getPlayer().getPosition().equals(this.getPosition())) {
            mapGenerator.addBattleList(this);
            mapGenerator.addBattleList(mapGenerator.getPlayer());
        }
    }

    @Override
    public void interact(MapGenerator mapGenerator) {
    }

    @Override
    public void battle(MapGenerator mapGenerator, Battle enemy) {
        // cannot battle with itself
        if (enemy == this)
            return;
        if (mapGenerator.playerIsInviceble()) {
            return;
        }
        // cannot battle when player is invisible
        if (mapGenerator.getPlayer().getIsInvisible())
            return;
        // battle with player
        if (enemy instanceof CharacterEntities && !((CharacterEntities) enemy).getIsInvinceble()) {
            enemy.setVita(enemy.getVita() - ((getVita() * getAttack()) / 10));
        } else if (enemy instanceof Mercenary && ((Mercenary) enemy).isAlly()) {
            enemy.setVita(enemy.getVita() - ((getVita() * getAttack()) / 10));
        }
        if (enemy.getVita() <= 0.0)
            mapGenerator.removeEntity((Entity) enemy);
    }

    private ArrayList<Direction> _obtainLegalMovement(List<Entity> entities) {
        ArrayList<Direction> res = new ArrayList<>();
        if (entities.stream().filter(e -> e.getPosition().equals(getPosition().translateBy(Direction.UP)))
                .noneMatch(e -> e instanceof Wall)) {
            res.add(Direction.UP);
        }
        if (entities.stream().filter(e -> e.getPosition().equals(getPosition().translateBy(Direction.DOWN)))
                .noneMatch(e -> e instanceof Wall)) {
            res.add(Direction.DOWN);
        }
        if (entities.stream().filter(e -> e.getPosition().equals(getPosition().translateBy(Direction.LEFT)))
                .noneMatch(e -> e instanceof Wall)) {
            res.add(Direction.LEFT);
        }
        if (entities.stream().filter(e -> e.getPosition().equals(getPosition().translateBy(Direction.RIGHT)))
                .noneMatch(e -> e instanceof Wall)) {
            res.add(Direction.RIGHT);
        }
        return res;
    }
}
