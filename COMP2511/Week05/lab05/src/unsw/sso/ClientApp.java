package unsw.sso;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import unsw.sso.providers.Hoogle;
import unsw.sso.providers.InstaHam;

public class ClientApp {
    private int hasHoogle = 0;
    private int hasInstaHam = 0;

    // HINT: Don't overcomplicate this
    //       for Task 2) you'll want some sort of object
    //       but don't go overboard, even in Task 4)
    //       this object can be relatively simple.
    private Map<String, Integer> usersExist = new HashMap<>();
    private final static int BOTH = 0, HOOGLE = 1, INSTAHAM = 2;
    private final String name;

    public ClientApp(String name) {
        this.name = name;
    }

    public String getName() {
        return name;
    }

    // TODO: you'll probably want to change a lot of this class
    public void registerProvider(Object o) {
        if (o instanceof Hoogle) {
            hasHoogle++;
        } else if (o instanceof InstaHam) {
            hasInstaHam++;
        }
    }

    public boolean hasHoogle() {
        return hasHoogle > 0;
    }

    public boolean hasInstaHam() {
        return hasInstaHam > 0;
    }

    public void registerUser(Token token, String provider) {
        // only hoogle is supported right now!  So we presume hoogle on user
        if (usersExist.get(token.getUserEmail()) != null) {
            usersExist.put(token.getUserEmail(), BOTH);
        } else {
            switch (provider) {
                case "Hoogle": usersExist.put(token.getUserEmail(), HOOGLE); break;
                case "InstaHam": usersExist.put(token.getUserEmail(), INSTAHAM); break;
            }
        }

    }

    public boolean hasUserForProvider(String email, Object provider) {
        return (provider instanceof InstaHam && this.hasInstaHam > 0 && usersExist.get(email) != HOOGLE) ||
                (provider instanceof Hoogle && this.hasHoogle > 0 && usersExist.get(email) != INSTAHAM);
    }

    public boolean hasProvider(String email) {
        return usersExist.get(email) != null;
    }

}
