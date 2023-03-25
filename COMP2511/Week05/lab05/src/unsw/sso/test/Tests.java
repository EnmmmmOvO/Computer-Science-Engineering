package unsw.sso.test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.IOException;

import org.junit.jupiter.api.Test;

import unsw.sso.ClientApp;
import unsw.sso.Browser;
import unsw.sso.providers.Hoogle;
import unsw.sso.providers.InstaHam;

/**
 * Extensive tests
 * 
 * @author Braedon Wooding
 */
public class Tests {
    @Test
    public void Task1_Cache() {
        // Create a provider
        Hoogle hoogle = new Hoogle();
        hoogle.addUser("user@hoogle.com.au", "1234");

        ClientApp app = new ClientApp("MyApp");
        // Allow users to login using hoogle
        app.registerProvider(hoogle);

        // Create a browser instance
        Browser browser = new Browser();
        browser.visit(app);

        // The rest of the 6 steps are identical to the readme example
        assertEquals(browser.getCurrentPageName(), "Select a Provider");
        browser.interact(hoogle);

        assertEquals(browser.getCurrentPageName(), "Hoogle Login");
        browser.interact(hoogle.generateFormSubmission("user@hoogle.com.au", "1234"));

        assertEquals(browser.getCurrentPageName(), "Home");
        assertTrue(app.hasUserForProvider("user@hoogle.com.au", hoogle));

        // now however if we redirect back to the same app we should stay on the home
        // page! Because of the cache
        browser.visit(app);
        assertEquals(browser.getCurrentPageName(), "Home");
        assertTrue(app.hasUserForProvider("user@hoogle.com.au", hoogle));

        // if it's a different instance though it shouldn't work
        ClientApp app2_butSame = new ClientApp("MyApp");
        browser.visit(app2_butSame);
        assertEquals(browser.getCurrentPageName(), "Select a Provider");

        browser.visit(app);
        assertEquals(browser.getCurrentPageName(), "Home");
        assertTrue(app.hasUserForProvider("user@hoogle.com.au", hoogle));
        browser.clearCache();
        // however, it should still stay on home here until we reload the page (/visit
        // it again)
        assertEquals(browser.getCurrentPageName(), "Home");
        assertTrue(app.hasUserForProvider("user@hoogle.com.au", hoogle));
        browser.visit(app);
        assertEquals(browser.getCurrentPageName(), "Select a Provider");

        // browsers don't share the cache
        Browser other = new Browser();
        other.visit(app);
        assertEquals(other.getCurrentPageName(), "Select a Provider");

        // an extension you could do here is if 2 applications share the same provider
        // they could share the same tokens... but not something we'll do in this lab
    }

    // this is more of a regression test to ensure your code
    // didn't break anything.
    @Test
    public void Task2_Regression() {
        ClientApp app = new ClientApp("MyApp");
        Browser browser = new Browser();
        Hoogle hoogle = new Hoogle();

        browser.visit(app);
        // no providers but it'll still show a select a provider screen
        assertEquals(browser.getCurrentPageName(), "Select a Provider");

        // hoogle is not registered so it shouldn't work
        browser.interact(hoogle);

        // Allow users to login using hoogle
        app.registerProvider(hoogle);

        // hoogle is now registered but it shouldn't allow any login
        browser.interact(hoogle);
        assertEquals(browser.getCurrentPageName(), "Hoogle Login");
        browser.interact(hoogle.generateFormSubmission("user@hoogle.com.au", "1234"));
        // the above will generate null causing you to go back to the list of providers
        assertEquals(browser.getCurrentPageName(), "Select a Provider");

        // But if we add a user...
        hoogle.addUser("user@hoogle.com.au", "1234");

        browser.interact(hoogle);
        browser.interact(hoogle.generateFormSubmission("user@hoogle.com.au", "1234"));
        // it should work!
        assertEquals(browser.getCurrentPageName(), "Home");
        assertTrue(app.hasUserForProvider("user@hoogle.com.au", hoogle));
    }

    // Testing going back a page
    @Test
    public void Task2_Regression_Back() {
        ClientApp app = new ClientApp("MyApp");
        Browser browser = new Browser();
        Hoogle hoogle = new Hoogle();
        hoogle.addUser("user@hoogle.com.au", "1234");
        app.registerProvider(hoogle);

        browser.visit(app);
        // no providers but it'll still show a select a provider screen
        assertEquals(browser.getCurrentPageName(), "Select a Provider");

        // null makes the browser backtrack
        browser.interact(null);
        assertEquals(browser.getCurrentPageName(), null);

        browser.visit(app);
        browser.interact(hoogle);
        assertEquals(browser.getCurrentPageName(), "Hoogle Login");
        browser.interact(null);
        assertEquals(browser.getCurrentPageName(), "Select a Provider");

        browser.interact(hoogle);
        assertEquals(browser.getCurrentPageName(), "Hoogle Login");
        browser.interact(hoogle.generateFormSubmission("badusername", "1234"));
        assertEquals(browser.getCurrentPageName(), "Select a Provider");

        browser.interact(hoogle);
        assertEquals(browser.getCurrentPageName(), "Hoogle Login");
        browser.interact(hoogle.generateFormSubmission("user@hoogle.com.au", "bad password"));
        assertEquals(browser.getCurrentPageName(), "Select a Provider");

        // good login
        browser.interact(hoogle);
        browser.interact(hoogle.generateFormSubmission("user@hoogle.com.au", "1234"));
        // it should work!
        assertEquals(browser.getCurrentPageName(), "Home");
        assertTrue(app.hasUserForProvider("user@hoogle.com.au", hoogle));

        browser.interact(null);
        // back to login
        assertEquals(browser.getCurrentPageName(), "Hoogle Login");
    }

    @Test
    public void Task2_Cache_Back() {
        ClientApp app = new ClientApp("MyApp");
        Browser browser = new Browser();
        Hoogle hoogle = new Hoogle();
        hoogle.addUser("user@hoogle.com.au", "1234");
        app.registerProvider(hoogle);

        browser.visit(app);
        // no providers but it'll still show a select a provider screen
        assertEquals(browser.getCurrentPageName(), "Select a Provider");

        // good login
        browser.interact(hoogle);
        browser.interact(hoogle.generateFormSubmission("user@hoogle.com.au", "1234"));
        // it should work!
        assertEquals(browser.getCurrentPageName(), "Home");
        assertTrue(app.hasUserForProvider("user@hoogle.com.au", hoogle));

        // reload to forget history
        browser.visit(app);
        assertEquals(browser.getCurrentPageName(), "Home");
        assertTrue(app.hasUserForProvider("user@hoogle.com.au", hoogle));

        // now if we try to go back it should go to null
        browser.interact(null);
        assertEquals(browser.getCurrentPageName(), null);
    }

    @Test
    public void Task3_InstaHam() throws IOException, InterruptedException {
        ClientApp app = new ClientApp("MyApp");
        Browser browser = new Browser();
        InstaHam instaham = new InstaHam();
        instaham.addUser("user@ham.com.au", browser);

        Hoogle hoogle = new Hoogle();
        hoogle.addUser("user@hoogle.com.au", "1234");

        // register ham but not hoogle
        app.registerProvider(instaham);

        browser.visit(app);
        assertEquals(browser.getCurrentPageName(), "Select a Provider");

        // we shouldn't be able to visit hoogle
        browser.interact(hoogle);
        assertEquals(browser.getCurrentPageName(), "Select a Provider");

        // but ham should work
        browser.interact(instaham);
        assertEquals(browser.getCurrentPageName(), "InstaHam Login");

        // valid user
        browser.interact("user@ham.com.au");
        Thread.sleep(800);

        // we should get an 'email'
        // and thus the browser should automatically log us in, however this isn't
        // instant
        // so we'll wait a second or two before triggering the check
        assertEquals(browser.getCurrentPageName(), "Home");
        assertTrue(app.hasUserForProvider("user@ham.com.au", instaham));

        // the cache should still work
        browser.visit(app);
        assertEquals(browser.getCurrentPageName(), "Home");
        assertTrue(app.hasUserForProvider("user@ham.com.au", instaham));
    }

    @Test
    public void Task3_InstaHam_MultipleUsers() throws InterruptedException {
        ClientApp app = new ClientApp("MyApp");
        Browser browser = new Browser();
        InstaHam instaham = new InstaHam();
        instaham.addUser("user2@ham.com.au", browser);

        Hoogle hoogle = new Hoogle();
        hoogle.addUser("user@hoogle.com.au", "1234");
        browser.visit(app);

        // register ham but not hoogle
        app.registerProvider(instaham);

        // if we have a different user it should choose the correct one
        instaham.addUser("user3@ham.com.au", browser);
        browser.interact(instaham);
        assertEquals(browser.getCurrentPageName(), "InstaHam Login");

        browser.interact("user2@ham.com.au");
        Thread.sleep(800);
        assertEquals(browser.getCurrentPageName(), "Home");
        assertTrue(app.hasUserForProvider("user2@ham.com.au", instaham));

        browser.interact(null);

        browser.interact("user3@ham.com.au");
        Thread.sleep(800);
        assertEquals(browser.getCurrentPageName(), "Home");
        assertTrue(app.hasUserForProvider("user3@ham.com.au", instaham));
    }

    @Test
    public void Task3_InstaHam_MultipleProviders() throws InterruptedException {
        ClientApp app = new ClientApp("MyApp");
        Browser browser = new Browser();
        InstaHam instaham = new InstaHam();
        instaham.addUser("user@hamANDhoogle.com.au", browser);

        Hoogle hoogle = new Hoogle();
        hoogle.addUser("user@hamANDhoogle.com.au", "1234");
        browser.visit(app);

        // register ham AND hoogle
        app.registerProvider(instaham);
        app.registerProvider(hoogle);

        browser.interact(instaham);
        assertEquals(browser.getCurrentPageName(), "InstaHam Login");

        browser.interact("user@hamANDhoogle.com.au");
        Thread.sleep(800);
        assertEquals(browser.getCurrentPageName(), "Home");
        assertTrue(app.hasUserForProvider("user@hamANDhoogle.com.au", instaham));
        assertFalse(app.hasUserForProvider("user@hamANDhoogle.com.au", hoogle));

        browser.interact(null);
        assertEquals(browser.getCurrentPageName(), "InstaHam Login");
        browser.interact(null);
        assertEquals(browser.getCurrentPageName(), "Select a Provider");
        browser.interact(hoogle);

        browser.interact(hoogle.generateFormSubmission("user@hamANDhoogle.com.au", "1234"));
        assertEquals(browser.getCurrentPageName(), "Home");
        assertTrue(app.hasUserForProvider("user@hamANDhoogle.com.au", instaham));
        assertTrue(app.hasUserForProvider("user@hamANDhoogle.com.au", hoogle));
    }

    @Test
    public void Task3_UsingIncorrectProviderOnWrongLogin() throws InterruptedException {
        ClientApp app = new ClientApp("MyApp");
        Browser browser = new Browser();
        InstaHam instaham = new InstaHam();
        instaham.addUser("user2@hamANDhoogle.com.au", browser);

        Hoogle hoogle = new Hoogle();
        hoogle.addUser("user2@hamANDhoogle.com.au", "1234");
        browser.visit(app);

        // register ham AND hoogle
        app.registerProvider(instaham);
        app.registerProvider(hoogle);

        browser.interact(hoogle);
        assertEquals(browser.getCurrentPageName(), "Hoogle Login");

        browser.interact("user2@hamANDhoogle.com.au");
        Thread.sleep(800);
        assertEquals(browser.getCurrentPageName(), "Select a Provider");

        browser.interact(instaham);
        browser.interact(hoogle.generateFormSubmission("user2@hamANDhoogle.com.au", "1234"));
        assertEquals(browser.getCurrentPageName(), "Select a Provider");
    }

    @Test
    public void Task4_LockingTestsSingleAndMultiProvider() throws InterruptedException {
        ClientApp app = new ClientApp("MyApp");
        Browser browser = new Browser();

        Hoogle hoogle = new Hoogle();
        hoogle.addUser("user3@hamANDhoogle.com.au", "1234");
        browser.visit(app);
        app.registerProvider(hoogle);

        // repeat 3 times
        for (int i = 0; i < 3; i++) {
            browser.interact(hoogle);
            assertEquals(browser.getCurrentPageName(), "Hoogle Login");
            browser.interact(hoogle.generateFormSubmission("user3@hamANDhoogle.com.au", "incorrect"));
            if (i < 2)
                assertEquals(browser.getCurrentPageName(), "Select a Provider");
            else
                assertEquals(browser.getCurrentPageName(), "Locked");
        }

        // not the user actually should still be registered
        assertTrue(app.hasUserForProvider("user3@hamANDhoogle.com.au", hoogle));

        // a locked user should be able to go back to select a provider
        browser.interact(null);
        assertEquals(browser.getCurrentPageName(), "Select a Provider");

        // but using that provider again should lock it agains
        browser.interact(hoogle);
        assertEquals(browser.getCurrentPageName(), "Hoogle Login");
        browser.interact(hoogle.generateFormSubmission("user3@hamANDhoogle.com.au", "incorrect"));
        assertEquals(browser.getCurrentPageName(), "Locked");

        // using a different provider though... should still result in a lock
        InstaHam instaham = new InstaHam();
        instaham.addUser("user3@hamANDhoogle.com.au", browser);
        app.registerProvider(instaham);

        browser.interact(null);
        assertEquals(browser.getCurrentPageName(), "Select a Provider");
        browser.interact(instaham);
        assertEquals(browser.getCurrentPageName(), "InstaHam Login");

        browser.interact("user3@hamANDhoogle.com.au");
        Thread.sleep(800);
        assertEquals(browser.getCurrentPageName(), "Locked");
        assertTrue(app.hasUserForProvider("user3@hamANDhoogle.com.au", instaham));
        assertTrue(app.hasUserForProvider("user3@hamANDhoogle.com.au", hoogle));

        // a different email should be fine though
        hoogle.addUser("user2@hoogle.com.au", "1234");
        browser.clearCache();
        browser.visit(app);
        browser.interact(hoogle);
        assertEquals(browser.getCurrentPageName(), "Hoogle Login");
        browser.interact(hoogle.generateFormSubmission("user2@hoogle.com.au", "1234"));
        assertEquals(browser.getCurrentPageName(), "Home");

        // even if we fail login twice we should still be able to login
        browser.clearCache();
        browser.visit(app);

        // repeat 2 times
        for (int i = 0; i < 2; i++) {
            browser.interact(hoogle);
            assertEquals(browser.getCurrentPageName(), "Hoogle Login");
            browser.interact(hoogle.generateFormSubmission("user2@hoogle.com.au", "12349"));
            assertEquals(browser.getCurrentPageName(), "Select a Provider");
        }

        browser.interact(hoogle);
        assertEquals(browser.getCurrentPageName(), "Hoogle Login");
        browser.interact(hoogle.generateFormSubmission("user2@hoogle.com.au", "1234"));
        assertEquals(browser.getCurrentPageName(), "Home");
    }

    @Test
    public void Task4_LockingTestsComplexCase_NoCache() throws InterruptedException {
        ClientApp app = new ClientApp("MyApp1");
        ClientApp app2 = new ClientApp("MyApp2");
        Browser browser = new Browser();

        Hoogle hoogle = new Hoogle();
        hoogle.addUser("user5@hamANDhoogle.com.au", "1234");

        InstaHam instaham = new InstaHam();
        instaham.addUser("user5@hamANDhoogle.com.au", browser);

        browser.visit(app);
        app.registerProvider(hoogle);
        app2.registerProvider(instaham);

        // repeat 3 times to lock
        for (int i = 0; i < 3; i++) {
            browser.interact(hoogle);
            assertEquals(browser.getCurrentPageName(), "Hoogle Login");
            browser.interact(hoogle.generateFormSubmission("user5@hamANDhoogle.com.au", "incorrect"));
            if (i < 2)
                assertEquals(browser.getCurrentPageName(), "Select a Provider");
            else
                assertEquals(browser.getCurrentPageName(), "Locked");
        }

        // not the user actually should be registered (but locked)
        assertTrue(app.hasUserForProvider("user5@hamANDhoogle.com.au", hoogle));

        // we can however login to the other website using the same email if it's
        // a different provider since the provider isn't registered on that website
        browser.visit(app2);
        browser.interact(instaham);
        assertEquals(browser.getCurrentPageName(), "InstaHam Login");
        browser.interact("user5@hamANDhoogle.com.au");
        Thread.sleep(800);
        assertEquals(browser.getCurrentPageName(), "Home");
        assertTrue(app2.hasUserForProvider("user5@hamANDhoogle.com.au", instaham));
        assertFalse(app2.hasUserForProvider("user5@hamANDhoogle.com.au", hoogle));

        app2.registerProvider(hoogle);
        // clear cache to make it simpler
        browser.clearCache();
        browser.visit(app2);
        browser.interact(instaham);
        assertEquals(browser.getCurrentPageName(), "InstaHam Login");
        browser.interact("user5@hamANDhoogle.com.au");
        Thread.sleep(800);
        assertEquals(browser.getCurrentPageName(), "Locked");

        // the user for the locked provider should be auto created as well
        assertTrue(app2.hasUserForProvider("user5@hamANDhoogle.com.au", instaham));
        assertTrue(app2.hasUserForProvider("user5@hamANDhoogle.com.au", hoogle));
    }

    @Test
    public void Task4_LockingTestsComplexCase_Cache() throws InterruptedException {
        ClientApp app = new ClientApp("MyApp1");
        ClientApp app2 = new ClientApp("MyApp2");
        Browser browser = new Browser();

        Hoogle hoogle = new Hoogle();
        hoogle.addUser("user6@hamANDhoogle.com.au", "1234");

        InstaHam instaham = new InstaHam();
        instaham.addUser("user6@hamANDhoogle.com.au", browser);

        browser.visit(app);
        app.registerProvider(hoogle);
        app2.registerProvider(instaham);

        // repeat 3 times to lock
        for (int i = 0; i < 3; i++) {
            browser.interact(hoogle);
            assertEquals(browser.getCurrentPageName(), "Hoogle Login");
            browser.interact(hoogle.generateFormSubmission("user6@hamANDhoogle.com.au", "incorrect"));
            if (i < 2)
                assertEquals(browser.getCurrentPageName(), "Select a Provider");
            else
                assertEquals(browser.getCurrentPageName(), "Locked");
        }

        // not the user actually should be registered (but locked)
        assertTrue(app.hasUserForProvider("user6@hamANDhoogle.com.au", hoogle));

        // we can however login to the other website using the same email if it's
        // a different provider since the provider isn't registered on that website
        browser.visit(app2);
        browser.interact(instaham);
        assertEquals(browser.getCurrentPageName(), "InstaHam Login");
        browser.interact("user6@hamANDhoogle.com.au");
        Thread.sleep(800);
        assertEquals(browser.getCurrentPageName(), "Home");
        assertTrue(app2.hasUserForProvider("user6@hamANDhoogle.com.au", instaham));
        assertFalse(app2.hasUserForProvider("user6@hamANDhoogle.com.au", hoogle));

        // if we then register hoogle it should prevent even a cache visit
        app2.registerProvider(hoogle);
        browser.visit(app2);
        assertEquals(browser.getCurrentPageName(), "Locked");
        assertTrue(app2.hasUserForProvider("user6@hamANDhoogle.com.au", instaham));
        assertTrue(app2.hasUserForProvider("user6@hamANDhoogle.com.au", hoogle));
    }
}
