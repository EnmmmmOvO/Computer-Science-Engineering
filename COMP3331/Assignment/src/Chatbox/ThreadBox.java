package Chatbox;

import User.User;

import java.io.*;
import java.util.*;

public class ThreadBox {
    private ArrayList<Thread> threadList;
    private File file;
    private String path = new File("").getAbsolutePath() + "/src/Chatbox/Source/Thread";

    public ThreadBox() {
        threadList = new ArrayList<>();
    }

    public void threadSet(User user, String title) {
        threadList.add(new Thread(title, user));
    }

    public void threadCreate(User user, String title) {
        threadList.add(new Thread(title, user));
        new File(path + '/' + title).mkdir();
        file = new File(path + '/' + title + "/" + title + ".txt");
        try {
            new File(path + '/' + title + "/" + title + ".txt").createNewFile();
            new File(path + '/' + title + "/information.txt").createNewFile();
        } catch (Exception e) {
            System.err.println("Cannot create txt Thread file");
            return;
        }

        file = new File(path + '/' + title + "/information.txt");
        BufferedWriter out = null;
        try {
            out = new BufferedWriter( new OutputStreamWriter(new FileOutputStream(file, true)));
            out.write(title + '\n');
            out.write(user.getName() + '\n');
            out.close();
        } catch (Exception e) {
            System.err.println("Cannot create txt Thread file");
        }
    }

    public int findThread(String title) {
        for (int loop = 0; loop <threadList.size(); loop++) {
            if (threadList.get(loop).getTitle().equals(title)) return loop;
        }
        return -1;
    }

    public void uploadThread(UserList userList) {
        file = new File(path);
        File[] fs = file.listFiles();
        for (int loop = 0; loop < fs.length; loop++) {
            //Upload Thread information
            File fileUpload = new File(path + '/' + fs[loop].getName() + "/information.txt");
            Scanner scanner = null;
            try{
                scanner = new Scanner(fileUpload);

            } catch (Exception e) {}
            String title;
            String input = scanner.nextLine();


            int loopStart = 0;
            StringBuilder stringBuilder = new StringBuilder();
            for (; loopStart < input.length(); loopStart++)
                stringBuilder.append(input.charAt(loopStart));
            title = stringBuilder.toString();
            input = scanner.nextLine();
            for (loopStart = 0, stringBuilder.delete(0, stringBuilder.length()); loopStart < input.length(); loopStart++)
                stringBuilder.append(input.charAt(loopStart));
            threadSet(userList.getUser(stringBuilder.toString()), title);
            int position = findThread(title);

            int temp = 0;
            try {
                input = scanner.nextLine();
            } catch (Exception e) {
                temp = 1;
            }

            // Upload file information
            while (temp == 0 && input != null) {
                stringBuilder.delete(0, stringBuilder.length());
                for (loopStart = 0; input.charAt(loopStart) != ' '; loopStart++)
                    stringBuilder.append(input.charAt(loopStart));
                String fileTitle = stringBuilder.toString();
                stringBuilder.delete(0, stringBuilder.length());
                for (loopStart++; loopStart < input.length(); loopStart++)
                    stringBuilder.append(input.charAt(loopStart));
                threadList.get(position).addFile(userList.getUser(stringBuilder.toString()), fileTitle);


                try {
                    input = scanner.nextLine();
                } catch (Exception e) {
                    break;
                }
            }

            //Upload Thread Message
            fileUpload = new File(path + '/' + fs[loop].getName() + '/' + fs[loop].getName() + ".txt");

            try {
                scanner = new Scanner(fileUpload);
                input = scanner.nextLine();
            } catch (Exception e) {
                continue;
            }

            while (input != null) {
                stringBuilder.delete(0, stringBuilder.length());
                if (checkMessageOrFile(input) == 0) {
                    for (loopStart = 0; input.charAt(loopStart) != ' '; loopStart++)
                    stringBuilder.append(input.charAt(loopStart));
                    User user = userList.getUser(stringBuilder.toString());
                    stringBuilder.delete(0, stringBuilder.length());
                    for (loopStart += 10; loopStart < input.length() && input.charAt(loopStart) != '\n'; loopStart++)
                        stringBuilder.append(input.charAt(loopStart));
                    threadList.get(position).addFileMessage(stringBuilder.toString(), user);
                } else {
                    for (loopStart = 2; input.charAt(loopStart) != ':'; loopStart++)
                        stringBuilder.append(input.charAt(loopStart));
                    User user = userList.getUser(stringBuilder.toString());

                    // Get content
                    stringBuilder.delete(0, stringBuilder.length());
                    for (loopStart += 2; loopStart < input.length() && input.charAt(loopStart) != '\n'; loopStart++)
                        stringBuilder.append(input.charAt(loopStart));

                    // Add new message
                    threadList.get(position).addMessage(stringBuilder.toString(), user);
                }

                try {
                    input = scanner.nextLine();
                } catch (Exception e) {
                    break;
                }
            }
        }
    }

    public int checkMessageOrFile(String input) {
        StringBuilder stringBuilder = new StringBuilder();
        int loop = 0;
        for (; input.charAt(loop) != ' '; loop++);
        for (loop++; input.charAt(loop) != ' '; loop++)
            stringBuilder.append(input.charAt(loop));
        return stringBuilder.toString().equals("uploaded") ? 0 : 1;
    }

    public void threadMessageAdd(User user, String content, String title) {
        Thread thread = threadList.get(findThread(title));
        thread.addMessage(content, user);
        file = new File(thread.getMessagePath());

        BufferedWriter out = null;
        try {
            out = new BufferedWriter( new OutputStreamWriter(new FileOutputStream(file, true)));

            String write = thread.getMessageSize() + " " + user.getName() + ": " + content;
            out.write(write + '\n');
            out.close();
        } catch (Exception e) {
            System.err.println("Cannot create txt Thread file");
            return;
        }
    }

    public String getList() {
        if (threadList.size() == 0) return "No threads to list";
        StringBuilder stringBuilder = new StringBuilder();
        for (int loop = 0; loop < threadList.size(); loop++) {
            stringBuilder.append(threadList.get(loop).getTitle());
            if (loop != threadList.size() - 1) stringBuilder.append(' ');
        }
        return stringBuilder.toString();
    }

    public String getThreadMessage(String title) {
        return threadList.get(findThread(title)).getThreadMessage();
    }

    public int deleteMessage(String title, String name, int number) {
        Thread t = threadList.get(findThread(title));
        int status = t.deleteMessage(name, number);
        if (status == 0) reWrite(title, t);
        return status;
    }

    public boolean deleteThread(String name, String title) {
        int position = findThread(title);
        if (!threadList.get(position).getThreadCreator().getName().equals(name))
            return false;
        threadList.remove(position);
        File deleteDir = new File(path + "/" + title);
        File[] deleteFile = deleteDir.listFiles();
        for (int loop = 0; loop < deleteFile.length; loop++)
            deleteFile[loop].delete();
        deleteDir.delete();
        return true;

    }
    public void reWrite(String title, Thread t) {
        String reWritePath = path + '/' + title + '/' + title + ".txt";
        for (int loop = 0; loop < t.getSize(); loop++) {
            try {
                BufferedWriter reWriterOut = loop == 0 ?
                        new BufferedWriter(new FileWriter(reWritePath)) :
                        new BufferedWriter(new FileWriter(reWritePath, true));
                reWriterOut.write(t.getMessage(loop) + '\n');
                reWriterOut.close();
            } catch (Exception e) {}
        }
    }
    public int editMessage(String title, String name, String content, int number) {
        Thread t = threadList.get(findThread(title));
        int status = t.editMessage(name, content, number);
        if (status == 0) reWrite(title, t);
        return status;
    }

    public void addFile(String title, User creator, String fileTitle) {
        threadList.get(findThread(title)).addFile(creator, fileTitle);
        file = new File(path + '/' + title + "/information.txt");
        BufferedWriter out = null;
        try {
            out = new BufferedWriter( new OutputStreamWriter(new FileOutputStream(file, true)));
            out.write(fileTitle + ' ' + creator.getName() + '\n');
            out.close();
        } catch (Exception e) {
            System.err.println("Cannot add file information");
            return;
        }

        file = new File(path + '/' + title + '/' + title + ".txt");
        try {
            out = new BufferedWriter( new OutputStreamWriter(new FileOutputStream(file, true)));
            out.write(creator.getName() + " uploaded " + fileTitle + ' ' + '\n');
            out.close();
        } catch (Exception e) {
            System.err.println("Cannot add file information");
        }

    }

    public boolean checkFileExist(String title, String fileTitle) {
        return threadList.get(findThread(title)).checkFileExist(fileTitle);
    }

    public String getAddFilePath(String title, String fileTitle) {
        return path + '/' + title + '/' + fileTitle;
    }

    public String getFilePath(String title, String fileTitle) {
        return threadList.get(findThread(title)).getFilePath(fileTitle);
    }
}
