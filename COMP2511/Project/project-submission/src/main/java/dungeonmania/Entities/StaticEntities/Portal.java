package dungeonmania.Entities.StaticEntities;

import dungeonmania.Entities.CharacterEntities.CharacterEntities;
import dungeonmania.Entities.Entity;
import dungeonmania.MapGenerator.MapGenerator;
import dungeonmania.util.Direction;
import dungeonmania.util.Position;

import java.util.List;

public class Portal extends StaticEntities {

    private String colour;

    public Portal(int x, int y, String colour) {
        super(x, y, 1, "portal", false);
        this.colour = colour;
    }

    @Override
    public void update(MapGenerator mapGenerator, Direction direction) {

        List<Entity> elist = mapGenerator.getEntities();
        Entity pairPortal = null;
        Entity player = null;

        for (Entity e : elist) {

            if (e != this && e instanceof Portal && ((Portal) e).getColour().equals(this.colour)) {
                pairPortal = e;
            } else if (e instanceof CharacterEntities) {
                player = e;
            }

        }

        if (player == null || pairPortal == null)
            return;

        Position p = player.getPosition().translateBy(direction);
        Position pairPortalPosition = pairPortal.getPosition();

        if (player.getPosition().translateBy(direction).equals(this.getPosition())
                && mapGenerator.getEntities().stream().filter(e -> e.getPosition().equals(p))
                        .noneMatch(e -> e instanceof Wall)
                && mapGenerator.getEntities().stream()
                        .filter(e -> e.getPosition().equals(pairPortalPosition.translateBy(direction)))
                        .noneMatch(e -> e instanceof Wall)) {

            player.setPosition(pairPortalPosition.getX(), pairPortalPosition.getY(), pairPortalPosition.getLayer());

        }
    }

    @Override
    public void interact(MapGenerator mapGenerator) {
        return;
    }

    public String getColour() {
        return colour;
    }

    @Override
    public Boolean isInteractable() {
        return false;
    }

}