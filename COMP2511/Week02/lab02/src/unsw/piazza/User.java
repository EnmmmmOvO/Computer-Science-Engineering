package unsw.piazza;

/**
 * A user of the Piazza forum
 */
public class User {

    private String name;

    /**
     * Creates a new user with the given name.
     * @param name
     */
    public User(String name) {
        this.name = name;
    }

    public String getName() {
        return name;
    }

    /**
     * Sets the user's name to the given name
     * @param name
     */
    public void setName(String name) {
        this.name = name;
    }

    @Override
    public boolean equals(Object o) {
        if (o.getClass() != this.getClass()) return false;
        if (!((User) o).name.equals(name)) return false;
        return true;
    }
}
