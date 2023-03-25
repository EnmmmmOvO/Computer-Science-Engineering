package unsw.archaic_fs;

import java.io.FileNotFoundException;

public class UNSWFileNotFoundException extends FileNotFoundException {
    public UNSWFileNotFoundException(String s) {
        super(s);
    }
}
