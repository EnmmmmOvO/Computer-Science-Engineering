package User;

public class User {
    private String name;
    private String password;
    private boolean online;

    public User(String name, String password) {
        this.name = name;
        this.password = password;
        this.online = false;
    }

    public User(String content) {
        this.name = separateName(content);
        this.password = separatePassword(content);
        this.online = false;
    }

    public boolean checkPassword(String passwordCheck) {
        return passwordCheck.equals(password);
    }

    public boolean checkUser(String nameCheck) {
        return name.equals(nameCheck);
    }

    public String getName() {
        return name;
    }

    public boolean getOnline() {
        return online;
    }

    public void setOnline(boolean online) {
        this.online = online;
    }

    public String separateName(String content) {
        StringBuilder stringBuilder = new StringBuilder();
        for (int loop = 0; content.charAt(loop) != ' ';  loop++)
            stringBuilder.append(content.charAt(loop));
        return stringBuilder.toString();
    }

    public String separatePassword(String content) {
        StringBuilder stringBuilder = new StringBuilder();
        int check = 0;
        for (int loop = 0; loop < content.length(); loop++) {
            if (content.charAt(loop) == ' ') {
                check = 1;
                continue;
            }
            if (content.charAt(loop) == '\n') break;
            if (check == 0) continue;
            stringBuilder.append(content.charAt(loop));
        }
        return stringBuilder.toString();
    }


}
