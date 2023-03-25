package dungeonmania.response.models;

import dungeonmania.util.Position;

public final class EntityResponse {
    private final String id;
    private final String type;
    private final Position position;
    private final boolean isInteractable;

    public EntityResponse(String id, String type, Position position, boolean isInteractable) {
        this.id = id;
        this.type = type;
        this.position = position;
        this.isInteractable = isInteractable;
    }

    public boolean isInteractable() {
        return isInteractable;
    }

    public final String getId() {
        return id;
    }

    public final String getType() {
        return type;
    }

    public final Position getPosition() {
        return position;
    }
}
