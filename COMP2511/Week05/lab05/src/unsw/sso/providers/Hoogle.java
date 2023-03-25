package unsw.sso.providers;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.UUID;

import unsw.sso.Token;
import unsw.sso.Browser;

public class Hoogle {
    private Map<String, String> userMappings = new HashMap<>();

    public void addUser(String email, String password) {
        userMappings.put(email, password);
    }

    public Token generateFormSubmission(String email, String password) {
        if (Objects.equals(userMappings.get(email), password)) {
            return new Token(UUID.randomUUID().toString(), email, getClass().getSimpleName());
        } else {
            return new Token(null, email, getClass().getSimpleName());
        }
    }
}
