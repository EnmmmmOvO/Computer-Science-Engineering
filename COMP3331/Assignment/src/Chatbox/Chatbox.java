package Chatbox;

public class Chatbox {
    private UserList userList;
    private ThreadBox threadList;

    public Chatbox() {
        userList = new UserList();
        threadList = new ThreadBox();
        threadList.uploadThread(userList);
    }

    public void addUser(String name, String content) {
        userList.addUser(name, content);
    }

    public boolean checkUser(String name) {
        return userList.findUser(name) != -1;
    }

    public boolean checkPassword(String name, String content) {
        return userList.checkUserPassword(name, content);
    }


    public void changeOnline(String name, boolean online) {
        userList.changeOnline(name, online);
    }

    public boolean checkOnline(String name) {
        return userList.checkOnline(name);
    }

    public boolean checkExisted(String title) {
        return threadList.findThread(title) != -1;
    }

    public void createThread(String title, String name) {
        threadList.threadCreate(userList.getUser(name), title);
    }

    public void sendMessageToThread(String title, String name, String content) {
        threadList.threadMessageAdd(userList.getUser(name), content, title);
    }

    public String getList() {
        return threadList.getList();
    }

    public String getThreadMessage(String title) {
        return threadList.getThreadMessage(title);
    }

    public int deleteMessage(String title, String name, int number) {
        return threadList.deleteMessage(title, name, number);
    }

    public boolean deleteThread(String title, String name) {
        return threadList.deleteThread(name, title);
    }

    public int editMessage(String title, String name, String content, int number) {
        return threadList.editMessage(title, name, content, number);
    }

    public void uploadFile(String title, String name, String fileTitle) {
        threadList.addFile(title, userList.getUser(name), fileTitle);
    }

    public boolean checkFileExist(String title, String fileTitle) {
        return threadList.checkFileExist(title, fileTitle);
    }

    public String getAddFilePath(String title, String fileTitle) {
        return threadList.getAddFilePath(title, fileTitle);
    }

    public String getFilePath(String title, String fileTitle) {
        return threadList.getFilePath(title, fileTitle);
    }

    public boolean checkUserOnline() {
        return userList.checkUserOnline();
    }

}
