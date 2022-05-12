

public class FileManage {
    private String title;
    private String path;
    private User creator;

    public FileManage(String title, String path, User creator) {
        this.title = title;
        this.path = path;
        this.creator = creator;
    }

    public String getPath() {
        return path;
    }

    public String getTitle() {
        return title;
    }
}
