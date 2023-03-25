package dungeonmania.util;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.net.URISyntaxException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import java.util.stream.Collectors;

public final class FileLoader {
    /**
     * Loads a resource file given a certain path that is relative to resources/
     * for example `/dungeons/maze.json`.  Will add a `/` prefix to path if it's not specified.
     * 
     * @param path Relative to resources/ will add an implicit `/` prefix if not given.
     * @return The textual content of the given file.
     * @throws IOException If the file doesn't exist / some other IO exception.
     */
    public static String loadResourceFile(String path) throws IOException {
        if (!path.startsWith("/"))
            path = "/" + path;
        try {
            return new String(Files.readAllBytes(Path.of(FileLoader.class.getResource(path).toURI())));
        } catch (URISyntaxException e) {
            throw new FileNotFoundException(path);
        }
    }

    /**
     * Lists file names (without extension) within a specified resource directory.
     * 
     * @param directory The directory relative to `resources` to look for files.  Will add a `/` prefix if it doesn't exist.
     *                  Typically is something like `/dungeons`
     * 
     * @return A list of *only* filenames with no extensions nor relative/absolute paths i.e. [maze, otherFile]
     * 
     * @throws IOException If directory path is invalid or some other sort of IO issue occurred.
     */
    public static List<String> listFileNamesInResourceDirectory(String directory) throws IOException {
        if (!directory.startsWith("/"))
            directory = "/" + directory;
        try {
            Path root = Paths.get(FileLoader.class.getResource(directory).toURI());
            return Files.walk(root).filter(Files::isRegularFile).map(x -> {
                String nameAndExt = x.toFile().getName();
                int extIndex = nameAndExt.lastIndexOf('.');
                return nameAndExt.substring(0, extIndex > -1 ? extIndex : nameAndExt.length());
            }).collect(Collectors.toList());
        } catch (URISyntaxException e) {
            throw new FileNotFoundException(directory);
        }
    }

    /**
     * Lists file names (without extension) within a specified non-resource directory.
     * 
     * @param directory A normal directory such as "mydirectory", relative to current working directory
     * 
     * @return A list of *only* filenames with no extensions nor relative/absolute paths i.e. [maze, otherFile]
     * 
     * @throws IOException If directory path is invalid or some other sort of IO issue occurred.
     */
    public static List<String> listFileNamesInDirectoryOutsideOfResources(String directory) throws IOException {
        Path root = Paths.get(directory);
        return Files.walk(root).filter(Files::isRegularFile).map(x -> {
            String nameAndExt = x.toFile().getName();
            int extIndex = nameAndExt.lastIndexOf('.');
            return nameAndExt.substring(0, extIndex > -1 ? extIndex : nameAndExt.length());
        }).collect(Collectors.toList());
    }
}
