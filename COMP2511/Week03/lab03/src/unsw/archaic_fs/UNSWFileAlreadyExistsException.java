package unsw.archaic_fs;

import java.io.FileNotFoundException;

public class UNSWFileAlreadyExistsException extends FileNotFoundException {
    public UNSWFileAlreadyExistsException(String s) {
        super(s);
    }
}
