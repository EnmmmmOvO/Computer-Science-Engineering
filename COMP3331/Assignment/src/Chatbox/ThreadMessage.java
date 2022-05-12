package Chatbox;

import User.User;

public class ThreadMessage {
    private User creator;
    private int status;
    private String content;
    private int num;

    private static final int MESSAGE = 0, FILE = 1;

    public ThreadMessage(User creator, String content, int status) {
        this.content = content;
        this.creator = creator;
        this.status = status;
        this.num = -1;
    }
    public ThreadMessage(User creator, String content, int status, int num) {
        this.content = content;
        this.creator = creator;
        this.status = status;
        this.num = num;
    }

    public User getCreator() {
        return creator;
    }

    public void setContent(String content) {
        this.content = content;
    }

    public int getNum() {
        return num;
    }

    public void setNum(int number) {
        this.num = number;
    }

    public int getStatus() {
        return status;
    }

    @Override
    public String toString() {
        if (status == MESSAGE) {
            return num + " " + creator.getName() + ": " + content;
        }
        return creator.getName() + " uploaded " + content;
    }
}
