package dungeonmania.Entities.MovingEntities;

import dungeonmania.Battle;
import dungeonmania.Entities.CharacterEntities.CharacterEntities;
import dungeonmania.Entities.Entity;
import dungeonmania.Entities.StaticEntities.Boulder;
import dungeonmania.MapGenerator.MapGenerator;
import dungeonmania.util.Direction;
import dungeonmania.util.Position;

import java.util.UUID;

public class Spider extends MovingEntities {

    private int tickTimes = 0;
    public boolean reverseDirection = false;
    private final Position[] movePath;
    private Double attack = 10.0;
    private Double vita = 10.0;

    public Spider(int x, int y) {
        super(x, y, 3, "spider", false);
        super.setEntityid(UUID.randomUUID().toString().replaceAll("-", "").substring(0, 7));

        movePath = new Position[] { new Position(x, y - 1), new Position(x + 1, y - 1), new Position(x + 1, y),
                new Position(x + 1, y + 1), new Position(x, y + 1), new Position(x - 1, y + 1), new Position(x - 1, y),
                new Position(x - 1, y - 1), };
    }

    @Override
    public void update(MapGenerator mapGenerator, Direction direction) {

        Position nextPosition = movePath[tickTimes % 8 < 0 ? tickTimes % 8 + 8 : tickTimes % 8];

        if (mapGenerator.getEntities().stream().filter(e -> e.getPosition().equals(nextPosition))
                .anyMatch(e -> e instanceof Boulder)) {
            reverseDirection = !reverseDirection;
        }

        setPosition(movePath[tickTimes % 8 < 0 ? tickTimes % 8 + 8 : tickTimes % 8]);

        if (reverseDirection) {
            tickTimes--;
        } else {
            tickTimes++;
        }

        if (mapGenerator.playerPosition().equals(this.getPosition())) {
            mapGenerator.getState().determin(mapGenerator, this, (Battle) mapGenerator.getPlayer());
        }

    }

    @Override
    public void battle(MapGenerator mapGenerator, Battle enemy) {
        if (mapGenerator.playerIsInviceble()) {
            return;
        }
        // cannot battle with itself
        if (enemy == this)
            return;
        // cannot battle when player is invisible
        if (mapGenerator.playerIsInvisible())
            return;
        // battle with player

        if (enemy instanceof CharacterEntities && !((CharacterEntities) enemy).getIsInvinceble()) {
            enemy.setVita(enemy.getVita() - ((getVita() * getAttack()) / 10));
        } else if (enemy instanceof Mercenary && ((Mercenary) enemy).isAlly()) {
            enemy.setVita(enemy.getVita() - ((getVita() * getAttack()) / 10));
        }

        if (enemy.getVita() <= 0.0) {
            mapGenerator.removeEntity((Entity) enemy);
            mapGenerator.removeEnemyList((Entity) enemy);
            return;
        }

    }

    @Override
    public void interact(MapGenerator mapGenerator) {
        return;
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

}
