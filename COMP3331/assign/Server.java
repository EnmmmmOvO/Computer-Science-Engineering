

import java.io.*;
import java.net.*;


public class Server {
    private static int serverPort;
    private static DatagramSocket socket;
    private static Message message = new Message();
    private static Chatbox chatbox;
    private static String thread;
    private static boolean checkSendBack = true;

    public static void main(String[] args) throws Exception {

        if (args.length != 1) {
            System.err.println("Required arguments: port");
            return;
        }
        serverPort = Integer.parseInt(args[0]);
        socket = new DatagramSocket(serverPort);
        chatbox = new Chatbox();
        System.out.println("Waiting for clients");

        serverStart();

    }

    private static void serverStart() throws Exception {
        while (true) {
            DatagramPacket request = new DatagramPacket(new byte[MAX_SIZE], MAX_SIZE);
            socket.receive(request);
            work(request);
        }
    }


    private static String getData(DatagramPacket datagramPacket) throws Exception {
        // Learned some code from PingServer.java which provided by COMP3331 Lab02.
        byte[] buf = datagramPacket.getData();
        ByteArrayInputStream bais = new ByteArrayInputStream(buf);
        InputStreamReader isr = new InputStreamReader(bais);
        BufferedReader br = new BufferedReader(isr);
        return br.readLine();
    }

    private static String getSendMessage(String content) {
        StringBuilder stringBuilder = new StringBuilder();
        int loop = 0;
        for (; content.charAt(loop) != ' '; loop++)
            stringBuilder.append(content.charAt(loop));
        thread = stringBuilder.toString();

        for (stringBuilder.delete(0, stringBuilder.length()), loop++; loop < content.length(); loop++)
            stringBuilder.append(content.charAt(loop));
        return stringBuilder.toString();

    }


    // temp
    private static void work(DatagramPacket request) throws Exception {
        checkSendBack = true;
        String line = getData(request);
        int clientPort = request.getPort();
        InetAddress clientHost = request.getAddress();

        int action = message.getAction(line);
        String username = message.getName(line);
        String content = message.getContent(line);

        byte[] buf = message.getMessage(action, SRS, username, "Success").getBytes();

        if (action > 1 && !chatbox.checkOnline(username)) {
            buf = message.getMessage(action, NGI, username, "Please Log in first").getBytes();
            socket.send(new DatagramPacket(buf, buf.length, clientHost, clientPort));
            return;
        }

        switch (action) {
            case FCT:
                System.out.println("Client authenticating");
                if (!chatbox.checkUser(username)) {
                    System.out.println("New user");
                } else if (chatbox.checkOnline(username)) {
                    System.out.println(username + " has already logged in");
                    buf = message.getMessage(action, SRF, username, username +
                            " has already logged in").getBytes();
                }
                break;

            case LOG:
                if (!chatbox.checkUser(username)) {
                    chatbox.addUser(username, content);
                    chatbox.changeOnline(username, true);
                    System.out.println(username + " successful logged in");
                } else if (!chatbox.checkPassword(username, content)) {
                    buf = message.getMessage(action, SRF, username, "Invalid password").getBytes();
                    System.out.println("Incorrect password");
                } else if (chatbox.checkOnline(username)) {
                    System.out.println(username + " has already logged in");
                    buf = message.getMessage(action, SRF, username, username +
                            " has already logged in").getBytes();
                } else {
                    chatbox.changeOnline(username, true);
                    System.out.println(username + " successful login");
                }
                break;

            case CRT:
                System.out.println(username + " issued CRT command");
                thread = content;
                if (chatbox.checkExisted(thread)) {
                    buf = message.getMessage(action, SRF, username, "Thread " + thread + " exists").getBytes();
                    System.out.println("Thread " + thread + " exists");
                } else {
                    chatbox.createThread(thread, username);
                    buf = message.getMessage(action, SRS, username, "Thread " + thread + " created").getBytes();
                    System.out.println("Thread " + thread + " created");
                }
                break;

            case MSG:
                System.out.println(username + " issued MSG command");
                String sendMessage = getSendMessage(content);
                if (!chatbox.checkExisted(thread)) {
                    buf = message.getMessage(action, SRF, username, "Thread " + thread +
                            " does not exist").getBytes();
                    System.out.println("Thread " + thread + " does not exist");
                } else {
                    chatbox.sendMessageToThread(thread, username, sendMessage);
                    buf = message.getMessage(action, SRS, username, "Message posted to " + thread +
                            " thread").getBytes();
                    System.out.println("Message posted to " + thread + " thread");
                }
                break;

            case DLT:
                System.out.println(username + " issued DLT command");
                int number = Integer.parseInt(getSendMessage(content));
                if (!chatbox.checkExisted(thread)) {
                    buf = message.getMessage(action, SRF, username, "Thread " + thread + " does not " +
                            "exist").getBytes();
                    System.out.println("Thread " + thread + " does not exist");
                } else {
                    int status = chatbox.deleteMessage(thread, username, number);
                    if (status == 0) {
                        System.out.println("Message has been deleted");
                        buf = message.getMessage(action, SRS, username, "The message has been " +
                                "deleted").getBytes();
                    } else if (status == 1) {
                        System.out.println("Message cannot be deleted");
                        buf = message.getMessage(action, SRF, username, "The message belongs to " +
                                "another user and cannot be deleted").getBytes();
                    } else if (status == 2) {
                        System.out.println("Message cannot be deleted");
                        buf = message.getMessage(action, SRF, username, "The message of the number " +
                                "does not exist").getBytes();
                    }
                }
                break;

            case EDT:
                System.out.println(username + " issued EDT command");

                StringBuilder stringBuilder = new StringBuilder();
                int loop = 0;
                for (; content.charAt(loop) != ' '; loop++)
                    stringBuilder.append(content.charAt(loop));
                thread = stringBuilder.toString();

                for (stringBuilder.delete(0, stringBuilder.length()), loop++; content.charAt(loop) != ' '; loop++)
                    stringBuilder.append(content.charAt(loop));
                int editNumber = Integer.parseInt(stringBuilder.toString());

                for (stringBuilder.delete(0, stringBuilder.length()), loop++; loop < content.length(); loop++)
                    stringBuilder.append(content.charAt(loop));

                if (!chatbox.checkExisted(thread)) {
                    buf = message.getMessage(action, SRF, username, "Thread " + thread + " does not " +
                            "exist").getBytes();
                    System.out.println("Thread " + thread + " does not exist");
                } else {
                    int status = chatbox.editMessage(thread, username, stringBuilder.toString(), editNumber);
                    if (status == 0) {
                        System.out.println("Message has been edited");
                        buf = message.getMessage(action, SRS, username, "The message has been " +
                                "edited").getBytes();
                    } else if (status == 1) {
                        System.out.println("Message cannot be edited");
                        buf = message.getMessage(action, SRF, username, "The message belongs to " +
                                "another user and cannot be edited").getBytes();
                    } else if (status == 2) {
                        System.out.println("Message cannot be edited");
                        buf = message.getMessage(action, SRF, username, "The message of the number " +
                                "does not exist").getBytes();
                    }
                }

                break;

            case LST:
                System.out.println(username + " issued LST command");
                String receiveContent = chatbox.getList();
                buf = receiveContent.equals("No threads to list") ?
                        message.getMessage(action, SRF, username, receiveContent).getBytes() :
                        message.getMessage(action, SRS, username, receiveContent).getBytes();
                break;

            case RDT:
                System.out.println(username + " issued RDT command");
                thread = content;
                if (!chatbox.checkExisted(thread)) {
                    buf = message.getMessage(action, SRF, username, "Thread " + thread + " does not " +
                            "exist").getBytes();
                    System.out.println("Thread " + thread + " does not exist");
                } else {
                    buf = message.getMessage(action, SRS, username, chatbox.getThreadMessage(thread)).getBytes();
                    System.out.println("Thread " + thread + " read");
                }
                break;

            case UPD:
                System.out.println(username + " issued UPD command");
                String fileTitle = getSendMessage(content);
                if (!chatbox.checkExisted(thread)) {
                    buf = message.getMessage(action, SRF, username, "Thread " + thread + " does not " +
                            "exist").getBytes();
                    System.out.println("Thread " + thread + " does not exist");
                    break;
                }
                if (chatbox.checkFileExist(thread, fileTitle)) {
                    buf = message.getMessage(action, SRF, username, "File " + fileTitle
                            + " had existed in Thread " + thread).getBytes();
                    System.out.println("File " + fileTitle + " had existed in Thread " + thread);
                    break;
                }
                checkSendBack = false;
                ServerSocket TCPServerSocket = new ServerSocket(0);
                buf = message.getMessage(action, SRS, username, Integer.toString(TCPServerSocket.getLocalPort())).
                        getBytes();
                socket.send(new DatagramPacket(buf, buf.length, clientHost, clientPort));

                Socket TCPSocket = TCPServerSocket.accept();
                InputStream inputStream = TCPSocket.getInputStream();
                
                // Learned some codes to convert the transmitted file into a byte[] that can be sent 
                // and how to convert the received byte[] into a file. 
                // https://www.cnblogs.com/debug-the-heart/p/13253886.html
                BufferedInputStream bufferedInputStream = new BufferedInputStream(inputStream);

                FileOutputStream fileOutputStream = new FileOutputStream(chatbox.getAddFilePath(thread, fileTitle));
                BufferedOutputStream bufferedOutputStream = new BufferedOutputStream(fileOutputStream);

                byte[] bytes = new byte[MAX_FILE_SIZE];
                int length;
                while ((length = bufferedInputStream.read(bytes)) != -1)
                    bufferedOutputStream.write(bytes, 0,length);
                bufferedOutputStream.flush();

                OutputStream out = TCPSocket.getOutputStream();
                String feedbackMessage = fileTitle + " uploaded to " + thread + " thread";
                out.write(feedbackMessage.getBytes());
                fileOutputStream.close();
                TCPServerSocket.close();
                TCPServerSocket.close();
                chatbox.uploadFile(thread, username, fileTitle);
                System.out.println(username + " uploaded file " + fileTitle + " " + thread + " thread");

                break;

            case DWN:
                System.out.println(username + " issued DWN command");
                String fileTitleDWN = getSendMessage(content);
                if (!chatbox.checkExisted(thread)) {
                    buf = message.getMessage(action, SRF, username, "Thread " + thread + " does not " +
                            "exist").getBytes();
                    System.out.println("Thread " + thread + " does not exist");
                    break;
                }
                if (!chatbox.checkFileExist(thread, fileTitleDWN)) {
                    buf = message.getMessage(action, SRF, username, "File does not exist in Thread "
                            + thread).getBytes();
                    System.out.println(fileTitleDWN + " does not exist in Thread " + thread);
                    break;
                }
                checkSendBack = false;
                buf = message.getMessage(action, SRS, username, "Require Port").getBytes();
                socket.send(new DatagramPacket(buf, buf.length, clientHost, clientPort));
                request = new DatagramPacket(new byte[MAX_SIZE], MAX_SIZE);
                socket.receive(request);
                getData(request);
                int ClientPost = Integer.parseInt(message.getContent(getData(request)));
                buf = message.getMessage(action, SRS, username, "Get port, prepare to Upload").getBytes();
                socket.send(new DatagramPacket(buf, buf.length, clientHost, clientPort));

                Socket TCPDWNSocket = new Socket(clientHost, ClientPost);


                // Learned some codes to convert the transmitted file into a byte[] that can be sent 
                // and how to convert the received byte[] into a file. 
                // https://www.cnblogs.com/debug-the-heart/p/13253886.html
                BufferedInputStream DWNBufferedInputStream = new BufferedInputStream(new FileInputStream(chatbox.
                        getFilePath(thread, fileTitleDWN)));
                byte[] DWNBytes = new byte[MAX_FILE_SIZE];
                int DWNLength;
                OutputStream outputStream = TCPDWNSocket.getOutputStream();
                BufferedOutputStream DWNBufferedOutputStream = new BufferedOutputStream(outputStream);
                while ((DWNLength = DWNBufferedInputStream.read(DWNBytes)) != -1)
                    DWNBufferedOutputStream.write(DWNBytes, 0,DWNLength);
                DWNBufferedOutputStream.flush();
                TCPDWNSocket.shutdownOutput();

                TCPDWNSocket.close();
                DWNBufferedInputStream.close();
                System.out.println(fileTitleDWN + " downloaded from Thread " + thread);

                break;

            case RMV:
                System.out.println(username + " issued RMV command");
                thread = content;
                if (!chatbox.checkExisted(thread)) {
                    buf = message.getMessage(action, SRF, username, "Thread " + thread + " does not " +
                            "exist").getBytes();
                    System.out.println("Thread " + thread + " does not exist");
                } else {
                    if (chatbox.deleteThread(thread, username)) {
                        buf = message.getMessage(action, SRF, username, "The thread has been removed").getBytes();
                        System.out.println("Thread " + thread + " removed");
                    } else {
                        buf = message.getMessage(action, SRF, username, "The thread was created " +
                                "by another user and cannot be removed").getBytes();
                        System.out.println("Thread " + thread + " cannot be removed");
                    }
                }
                break;


            case XIT:
                chatbox.changeOnline(username, false);
                System.out.println(username + " " + content);
                if (!chatbox.checkUserOnline()) System.out.println("Waiting for clients");
                break;

            default: break;
        }
        if (checkSendBack) socket.send(new DatagramPacket(buf, buf.length, clientHost, clientPort));
    }

    private static final int
        FCT = 0,
        LOG = 1,
        CRT = 2,
        MSG = 3,
        DLT = 4,
        EDT = 5,
        LST = 6,
        RDT = 7,
        UPD = 8,
        DWN = 9,
        RMV = 10,
        XIT = 11,

        SRS = 0,
        SRF = 1,
        CTS = 2,
        NGI = 3,

        MAX_SIZE = 1024,
        MAX_FILE_SIZE = 102400;
}

