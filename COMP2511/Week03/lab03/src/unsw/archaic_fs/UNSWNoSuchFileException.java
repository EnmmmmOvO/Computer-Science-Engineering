package unsw.archaic_fs;

import java.io.FileNotFoundException;

public class UNSWNoSuchFileException extends FileNotFoundException {
    public UNSWNoSuchFileException(String s) {
        super(s);
    }
}
