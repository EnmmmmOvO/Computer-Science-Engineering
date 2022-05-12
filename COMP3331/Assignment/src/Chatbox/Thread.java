package Chatbox;

import FileManage.FileManage;
import User.User;

import java.io.File;
import java.util.*;

public class Thread {
    private ArrayList<ThreadMessage> thread;
    private ArrayList<FileManage> fileManage;
    private int messageSize = 0;
    private String title;
    private User threadCreator;
    private String path = new File("").getAbsolutePath() + "/src/Chatbox/Source/Thread";
    private static final int MESSAGE = 0, FILE = 1;


    public Thread(String title, User threadCreator) {
        this.title = title;
        this.threadCreator = threadCreator;
        thread = new ArrayList<>();
        path = path + '/' + title;
        fileManage = new ArrayList<>();
    }

    public void addMessage(String content, User user) {
        messageSize++;
        thread.add(new ThreadMessage(user, content, MESSAGE, messageSize));
    }

    public void addFileMessage(String title, User user) {
        thread.add(new ThreadMessage(user, title, FILE));
    }

    public String getTitle() {
        return title;
    }

    public String getMessagePath() {
        return path + '/' + title + ".txt";
    }

    public int getMessageSize() {
        return messageSize;
    }

    public User getThreadCreator() {
        return threadCreator;
    }

    public int getSize() {
        return thread.size();
    }

    public String getThreadMessage() {
        if (thread.size() == 0) return "Thread " + title + " is empty";
        StringBuilder stringBuilder = new StringBuilder();
        for (int loop = 0; loop < thread.size(); loop++) {
            stringBuilder.append(thread.get(loop).toString());
            if (loop != thread.size() - 1) stringBuilder.append(';');
        }
        return stringBuilder.toString();
    }

    public int deleteMessage(String name, int number) {
        for (int loop = 0; loop < thread.size(); loop++) {
            if (thread.get(loop).getNum() == number) {
                if (thread.get(loop).getCreator().getName().equals(name)) {
                    thread.remove(loop);
                    messageSize--;
                    for (int loopReset = 0, loopNum = 1; loopReset < thread.size(); loopReset++) {
                        if (thread.get(loopReset).getStatus() == MESSAGE) {
                            thread.get(loopReset).setNum(loopNum);
                            loopNum++;
                        }
                    }
                    return 0;
                } else {
                    return 1;
                }
            }
        }
        return 2;
    }

    public String getMessage(int number) {
        return thread.get(number).toString();
    }

    public int editMessage(String name, String content, int number) {
        for (int loop = 0; loop < thread.size(); loop++) {
            if (thread.get(loop).getNum() == number) {
                if (thread.get(loop).getCreator().getName().equals(name)) {
                    thread.get(loop).setContent(content);
                    return 0;
                } else {
                    return 1;
                }
            }
        }
        return 2;
    }

    public void addFile(User creator, String title) {
        fileManage.add(new FileManage(title, path + '/' + title, creator));
        thread.add(new ThreadMessage(creator, title, FILE));
    }

    public boolean checkFileExist(String fileTitle) {
        for (int loop = 0; loop < fileManage.size(); loop++) {
            if (fileManage.get(loop).getTitle().equals(fileTitle)) {
                return true;
            }
        }
        return false;
    }

    public String getFilePath(String fileTitle) {
        int loop = 0;
        for (; loop < fileManage.size(); loop++)
            if (fileManage.get(loop).getTitle().equals(fileTitle)) break;
        return fileManage.get(loop).getPath();
    }

}
