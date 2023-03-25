package unsw.sso;

import java.time.LocalDateTime;
import java.time.temporal.ChronoUnit;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

import unsw.sso.providers.Hoogle;
import unsw.sso.providers.InstaHam;

public class Browser {
    private Token currentToken = null;
    private String currentPage = null;
    private String previousPage = null;
    private ClientApp currentApp = null;
    private Map<ClientApp, Token> cache = new HashMap<>();
    private InstaHam instaHam = null;

    private ArrayList<Locked> locked = new ArrayList<>();

    private class Locked{
        int time;
        ClientApp app;
        boolean locked;
        String email;

        Locked(ClientApp app, String email) {
            this.time = 1;
            this.app = app;
            this.email = email;
            this.locked = false;
        }
    }

    public void visit(ClientApp app) {
        currentToken = cache.get(app);
        if (currentToken != null && locked.stream().anyMatch(m -> currentToken.getUserEmail().equals(m.email) && m.locked)) {
            this.currentPage = "Locked";
            app.registerUser(currentToken, "Hoogle");
            app.registerUser(currentToken, "InstaHam");
            return;
        }
        previousPage = app.equals(currentApp) ? null : currentPage;
        this.currentPage = currentToken == null ? "Select a Provider" : "Home";
        this.currentApp = app;
    }

    public String getCurrentPageName() {
        return this.currentPage;
    }

    public void clearCache() {
        cache.clear();
    }

    public void interact(Object using) {
        if (using == null) {

            if (this.currentPage.equals("Locked")) {
                this.currentPage = "Select a Provider";
                this.previousPage = null;
            } else {
                this.currentPage = previousPage;
                if (previousPage == null) return;
                switch (previousPage) {
                    case "Select a Provider":
                        previousPage = null;
                        break;
                    case "Hoogle Login":
                    case "InstaHam Login":
                        previousPage = "Select a Provider";
                        break;
                }
            }
            return;
        }

        switch (currentPage) {
            case "Select a Provider": {
                // if the currentApp doesn't have hoogle
                // then it has no providers, which just will prevent
                // transition.
                if (using instanceof Hoogle && currentApp.hasHoogle()) {
                    this.previousPage = currentPage;
                    this.currentPage = "Hoogle Login";
                } else if (using instanceof InstaHam && currentApp.hasInstaHam()) {
                    this.previousPage = currentPage;
                    this.currentPage = "InstaHam Login";
                    instaHam = (InstaHam) using;
                }
                break;
            }

            case "Hoogle Login": {
                if (using instanceof Token &&
                        ((Token) using).getProviderName().equals(new Hoogle().getClass().getSimpleName())) {
                    this.previousPage = currentPage;
                    if (((Token) using).getAccessToken() == null) {
                        Locked temp = null;
                        for (Locked m : locked) {
                            if (m.app.equals(currentApp) && m.email.equals(((Token) using).getUserEmail())) {
                                temp = m;
                                break;
                            }
                        }

                        if (temp != null) {
                            switch (temp.time) {
                                case 1: {
                                    temp.time++;
                                    this.currentPage = "Select a Provider";
                                    break;
                                }
                                default: {
                                    temp.time = 3;
                                    temp.locked = true;
                                    this.currentPage = "Locked";
                                    break;
                                }
                            }
                        } else {
                            locked.add(new Locked(currentApp, ((Token) using).getUserEmail()));
                            this.currentPage = "Select a Provider";
                        }

                        this.currentToken = (Token)using;
                        this.currentApp.registerUser((Token)using, "Hoogle");
                        return;
                    }
                    this.currentPage = "Home";

                    // tell client application about us
                    this.currentToken = (Token)using;
                    this.currentApp.registerUser((Token)using, "Hoogle");

                    // record the cache
                    this.cache.put(currentApp, currentToken);
                } else {
                    this.currentPage = previousPage;
                }
                break;
            }

            case "InstaHam Login": {
                if (using instanceof String) {
                    instaHam.broadcastCode((String) using);
                } else if (using instanceof Token &&
                        ((Token) using).getProviderName().equals(new InstaHam().getClass().getSimpleName())) {
                    if (locked.stream().anyMatch(m -> m.app.equals(currentApp) &&
                            m.email.equals(((Token) using).getUserEmail()) && m.locked)) {
                        this.currentPage = "Locked";
                        return;
                    }
                    if (currentApp.hasProvider(((Token) using).getUserEmail()) &&
                            locked.stream().anyMatch(m -> m.email.equals(((Token) using).getUserEmail()) && m.locked)) {
                        this.currentPage = "Locked";
                        this.currentApp.registerUser((Token)using, "Hoogle");
                        return;
                    }

                    this.previousPage = currentPage;
                    this.currentPage = ((Token) using).getAccessToken() == null ? "Select a Provider" : "Home";

                    // tell client application about us
                    this.currentToken = (Token)using;
                    this.currentApp.registerUser((Token)using, "InstaHam");

                    // record the cache
                    this.cache.put(currentApp, currentToken);
                } else {
                    this.currentPage = previousPage;
                }
            }

            case "Home": case "Locked": break;
        }
    }
}
