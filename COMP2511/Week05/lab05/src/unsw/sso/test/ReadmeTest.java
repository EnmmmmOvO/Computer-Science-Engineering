package unsw.sso.test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import org.junit.jupiter.api.Test;

import unsw.sso.ClientApp;
import unsw.sso.Browser;
import unsw.sso.providers.Hoogle;

/**
 * Simple test from readme
 * 
 * @author Braedon Wooding
 */
public class ReadmeTest {
    // Your code should already pass this!
    @Test
    public void testReadme() {
        // Create a provider
        Hoogle hoogle = new Hoogle();
        hoogle.addUser("user@hoogle.com.au", "1234");

        ClientApp app = new ClientApp("MyApp");
        // Allow users to login using hoogle
        app.registerProvider(hoogle);

        // Create a browser instance
        Browser browser = new Browser();

        // Visit our client application
        browser.visit(app);

        // Since the browser has no initial login credentials
        // it'll cause us to redirect to a page to select providers
        assertEquals(browser.getCurrentPageName(), "Select a Provider");

        // Since we are on the provider selection page we can 'interact' with the page
        // and through that select a provider. Interaction takes in a single `Object`
        browser.interact(hoogle);

        assertEquals(browser.getCurrentPageName(), "Hoogle Login");

        // since we are on the provider form
        // we can interact and provide a form submission
        browser.interact(hoogle.generateFormSubmission("user@hoogle.com.au", "1234"));

        // This should inform the browser that the form is filled
        // Which will then authenticate the form with the third party provider
        // which causes the browser to redirect back to the login page with token
        // which causes the client application to validate the token
        // resulting in a redirect back to the home page.
        assertEquals(browser.getCurrentPageName(), "Home");
        assertTrue(app.hasUserForProvider("user@hoogle.com.au", hoogle));
    }
}
