package unsw.test;

import org.junit.jupiter.api.Test;

import unsw.archaic_fs.*;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.EnumSet;

public class ArchaicFsTest {
    @Test
    public void testCdInvalidDirectory() {
        ArchaicFileSystem fs = new ArchaicFileSystem();

        // Try to change directory to an invalid one
        assertThrows(UNSWNoSuchFileException.class, () -> {
            fs.cd("/usr/bin/cool-stuff");
        });
    }

    @Test
    public void testCdValidDirectory() {
        ArchaicFileSystem fs = new ArchaicFileSystem();

        assertDoesNotThrow(() -> {
            fs.mkdir("/usr/bin/cool-stuff", true, false);
            fs.cd("/usr/bin/cool-stuff");
        });
    }

    @Test
    public void testCdAroundPaths() {
        ArchaicFileSystem fs = new ArchaicFileSystem();

        assertDoesNotThrow(() -> {
            fs.mkdir("/usr/bin/cool-stuff", true, false);
            fs.cd("/usr/bin/cool-stuff");
            assertEquals("/usr/bin/cool-stuff", fs.cwd());
            fs.cd("..");
            assertEquals("/usr/bin", fs.cwd());
            fs.cd("../bin/..");
            assertEquals("/usr", fs.cwd());
        });
    }

    @Test
    public void testCreateFile() {
        ArchaicFileSystem fs = new ArchaicFileSystem();

        assertDoesNotThrow(() -> {
            fs.writeToFile("test.txt", "My Content", EnumSet.of(FileWriteOptions.CREATE, FileWriteOptions.TRUNCATE));
            assertEquals("My Content", fs.readFromFile("test.txt"));
            fs.writeToFile("test.txt", "New Content", EnumSet.of(FileWriteOptions.TRUNCATE));
            assertEquals("New Content", fs.readFromFile("test.txt"));
        });
    }

    @Test
    public void testTruncateAppend() {
        ArchaicFileSystem fs = new ArchaicFileSystem();

        assertThrows(IllegalArgumentException.class, ()-> {
            fs.writeToFile("test.txt", "My Content", EnumSet.of(FileWriteOptions.APPEND, FileWriteOptions.TRUNCATE));
        });
    }

    @Test
    public void testAppendFile() {
        ArchaicFileSystem fs = new ArchaicFileSystem();

        assertDoesNotThrow(() -> {
            fs.writeToFile("test.txt", "My Content", EnumSet.of(FileWriteOptions.CREATE, FileWriteOptions.TRUNCATE));
            assertEquals("My Content", fs.readFromFile("test.txt"));
            fs.writeToFile("test.txt", " is the best", EnumSet.of(FileWriteOptions.APPEND));
            assertEquals("My Content is the best", fs.readFromFile("test.txt"));
        });
    }

    @Test
    public void testCdRootDir() {
        ArchaicFileSystem fs = new ArchaicFileSystem();

        assertDoesNotThrow(() -> {
            fs.cd("..");
            assertEquals("", fs.cwd());
        });
    }


    @Test
    public void testCdFile() {
        ArchaicFileSystem fs = new ArchaicFileSystem();

        assertThrows(UNSWNoSuchFileException.class, () -> {
            fs.writeToFile("My Content.txt", "My Content", EnumSet.of(FileWriteOptions.CREATE, FileWriteOptions.TRUNCATE));
            fs.cd("My Content.txt");
        });
    }
    @Test
    public void testNotCreateAFile() {
        ArchaicFileSystem fs = new ArchaicFileSystem();

        assertThrows(UNSWFileNotFoundException.class, () -> {
            fs.writeToFile("My Content.txt", "My Content", EnumSet.of(FileWriteOptions.TRUNCATE));
        });
    }



        // Now write some more!
    // Some ideas to spark inspiration;
    // - File Writing/Reading with various options (appending for example)
    // - Cd'ing .. on the root most directory (shouldn't error should just remain on root directory)
    // - many others...
}