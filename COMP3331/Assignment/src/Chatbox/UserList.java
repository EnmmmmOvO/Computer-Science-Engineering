package Chatbox;

import User.*;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileOutputStream;
import java.io.OutputStreamWriter;
import java.util.ArrayList;
import java.util.Scanner;

public class UserList {
    private static ArrayList<User> userList;

    private static File file = new File("src/Chatbox/Source/credentials.txt");

    public UserList() {
        userList = new ArrayList<>();
        try {
            Scanner scanner = new Scanner(file);
            String line = scanner.nextLine();
            for (; line != null; line = scanner.nextLine()) {
                userList.add(new User(line));
            }
        } catch (Exception e) {}
    }

    public void addUser(String name, String content) {
        userList.add(new User(name, content));
        BufferedWriter out = null;
        try {
            out = new BufferedWriter( new OutputStreamWriter(new FileOutputStream(file, true)));
            out.write(name + " " + content + "\n");
        } catch (Exception e) {
            System.err.println("User cannot add in file successfully");
        } finally {
            try {
                out.close();
            } catch (Exception e) {}
        }
    }

    public int findUser(String name) {
        for (int loop = 0; loop < userList.size(); loop++) {
            if (userList.get(loop).checkUser(name)) {
                return loop;
            }
        }
        return -1;
    }

    public User getUser(String name) {
        return userList.get(findUser(name));
    }

    public boolean checkUserPassword(String name, String content) {
        return userList.get(findUser(name)).checkPassword(content);
    }

    public void changeOnline(String name, boolean online) {
        userList.get(findUser(name)).setOnline(online);
    }

    public boolean checkOnline(String name)  {
        return userList.get(findUser(name)).getOnline();
    }

    public void onlineStatus() {
        for (int loop = 0; loop < userList.size(); loop++)
            if (userList.get(loop).getOnline()) System.out.println(userList.get(loop).getName());

    }

    public boolean checkUserOnline() {
        for (int loop = 0; loop < userList.size(); loop++)
            if (userList.get(loop).getOnline()) return true;
        return false;
    }

}
