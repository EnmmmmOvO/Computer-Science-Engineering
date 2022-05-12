package Client;


import java.io.*;
import java.net.*;
import java.util.*;

import Message.*;


public class Client {
    private static DatagramSocket socket;
    private static DatagramPacket packet;
    private static int serverPort;
    private static InetAddress serverHost;
    private static Scanner scanner = new Scanner(System.in);
    private static Message message= new Message();

    public static void main(String[] args) throws Exception {

        if (args.length != 1) {
            System.err.println("Required arguments: port");
            return;
        }

        // Set Server Information
        serverPort = Integer.parseInt(args[0]);
        serverHost = InetAddress.getByName("127.0.0.1");

        socket = new DatagramSocket();
        socket.setSoTimeout(TIMEOUT);
        String username = null;

        // User information enter
        boolean check = false;

        while (!check) {
            // Authenticate username
            System.out.print("Enter username: ");

            try {
                username = scanner.nextLine();
            } catch (Exception e) {
                System.err.println("Please enter your username!");
                continue;
            }
            sendMessage(message.getMessage(FCT, CTS, username,  "Log in"));

            // Authenticate user password
            System.out.print("Enter password: ");
            String userPassword;
            try {
                userPassword = scanner.nextLine();
            } catch (Exception e) {
                System.err.println("Please enter your password!");
                continue;
            }
            sendMessage(message.getMessage(LOG, CTS, username, userPassword));

            if (message.getStatus(getData(packet)) == SRS) {
                System.out.println("Welcome to the forum");
                check = true;
            } else {
                System.out.println(message.getContent(getData(packet)));
            }
        }

        while (check) {
            System.out.print("Enter one of the following commands: CRT, MSG, DLT, EDT, LST, RDT, UPD, DWN, RMV, XIT: ");
            String input = scanner.nextLine();
            int action = StringtoInt(input);
            String content = getInputInformation(input);
            switch (action) {
                case CRT:
                    if (content == null) {
                        System.out.println("Incorrect syntax for CRT");
                        break;
                    }
                    boolean checkCRT = true;
                    for (int loop = 0; loop < content.length(); loop++) {
                        if (content.charAt(loop) == ' ' && loop != content.length() - 1) {
                            System.out.println("Incorrect syntax for CRT");
                            checkCRT = false;
                            break;
                        }
                    }
                    if (!checkCRT) break;

                    sendMessage(message.getMessage(CRT, CTS, username, content));
                    System.out.println(message.getContent(getData(packet)));

                    break;

                case MSG:
                    if (content == null) {
                        System.out.println("Incorrect syntax for MSG (Loss Thread and Message)");
                        break;
                    }
                    int loopMSG = 0;
                    for (; loopMSG < content.length() && content.charAt(loopMSG) != ' '; loopMSG++);
                    if (loopMSG == content.length() || loopMSG == content.length() - 1) {
                        System.out.println("Incorrect syntax for MSG (Loss Message)");
                        break;
                    }

                    sendMessage(message.getMessage(MSG, CTS, username, content));
                    System.out.println(message.getContent(getData(packet)));
                    break;

                case DLT:
                    if (content == null) {
                        System.out.println("Incorrect syntax for DLT (Loss Thread and Number)");
                        break;
                    }
                    int loopDLT = 0;
                    for (; loopDLT < content.length() && content.charAt(loopDLT) != ' '; loopDLT++);
                    if (loopDLT == content.length() ) {
                        System.out.println("Incorrect syntax for DLT (Loss Number)");
                        break;
                    }
                    boolean checkDLT = true;
                    for (loopDLT++; loopDLT < content.length(); loopDLT++) {
                        if (!Character.isDigit(content.charAt(loopDLT))) {
                            checkDLT = false;
                            System.out.println("Incorrect syntax for DLT (Wrong number)");
                            break;
                        }
                    }
                    if (!checkDLT) break;

                    sendMessage(message.getMessage(DLT, CTS, username, content));
                    System.out.println(message.getContent(getData(packet)));
                    break;

                case EDT:
                    if (content == null) {
                        System.out.println("Incorrect syntax for EDT (Loss Thread, Number and Message)");
                        break;
                    }
                    int loopEDT = 0;
                    for (; loopEDT < content.length() && content.charAt(loopEDT) != ' '; loopEDT++);
                    if (loopEDT == content.length() ||
                            (loopEDT == content.length() - 1 && content.charAt(loopEDT) == ' ')) {
                        System.out.println("Incorrect syntax for EDT (Loss Number and Message)");
                        break;
                    }
                    boolean checkEDT = true;
                    for (loopEDT++ ; loopEDT < content.length() && content.charAt(loopEDT) != ' '; loopEDT++) {
                        if (!Character.isDigit(content.charAt(loopEDT))) {
                            checkEDT = false;
                            System.out.println("Incorrect syntax for EDT (Wrong number)");
                            break;
                        }
                    }
                    if (!checkEDT) break;
                    if (loopEDT == content.length() ||
                            (loopEDT == content.length() - 1 && content.charAt(loopEDT) == ' ')) {
                        System.out.println("Incorrect syntax for EDT (Loss Message)");
                        break;
                    }

                    sendMessage(message.getMessage(EDT, CTS, username, content));
                    System.out.println(message.getContent(getData(packet)));
                    break;

                case LST:
                    if (content != null) {
                        System.out.println("Incorrect syntax for LST");
                        break;
                    }

                    sendMessage(message.getMessage(LST, CTS, username, "LST"));
                    if (message.getStatus(getData(packet)) == SRF) {
                        System.out.println(message.getContent(getData(packet)));
                    } else {
                        System.out.println("The list of active threads:");
                        String print = message.getContent(getData(packet));
                        for (int loop = 0; loop < print.length(); loop++)
                            System.out.print(print.charAt(loop) == ' ' ? '\n' : print.charAt(loop));
                        System.out.print('\n');
                    }
                    break;

                case RDT:
                    if (content == null) {
                        System.out.println("Incorrect syntax for RDT");
                        break;
                    }
                    boolean checkRDT = true;
                    for (int loop = 0; loop < content.length(); loop++) {
                        if (content.charAt(loop) == ' ' && loop != content.length() - 1) {
                            System.out.println("Incorrect syntax for RDT");
                            checkRDT = false;
                            break;
                        }
                    }
                    if (!checkRDT) break;

                    sendMessage(message.getMessage(RDT, CTS, username, content));
                    if (message.getStatus(getData(packet)) == SRF) {
                        System.out.println(message.getContent(getData(packet)));
                    } else {
                        String print = message.getContent(getData(packet));
                        for (int loop = 0; loop < print.length(); loop++)
                            System.out.print(print.charAt(loop) == ';' ? '\n' : print.charAt(loop));
                        System.out.print('\n');
                    }
                    break;

                case UPD:
                    if (content == null) {
                        System.out.println("Incorrect syntax for UPD (Loss Thread and Message)");
                        break;
                    }
                    int loopUPD = 0;
                    for (; loopUPD < content.length() && content.charAt(loopUPD) != ' '; loopUPD++);
                    if (loopUPD == content.length() || loopUPD == content.length() - 1) {
                        System.out.println("Incorrect syntax for UPD (Loss Message)");
                        break;
                    }
                    boolean checkUPD = true;
                    StringBuilder stringBuilderUPD = new StringBuilder();
                    for (loopUPD++; loopUPD < content.length(); loopUPD++) {
                        if (content.charAt(loopUPD) == ' ' && loopUPD != content.length() - 1) {
                            checkUPD = false;
                            System.out.println("Incorrect syntax for UPD (Input more argument)");
                            break;
                        }
                        stringBuilderUPD.append(content.charAt(loopUPD));
                    }
                    if (!checkUPD) break;

                    String pathUPD = new File("").getAbsolutePath() + "/src/Client/Resource/Upload";
                    File[] fsUPD = new File(pathUPD).listFiles();
                    boolean checkFileUPD = false;
                    for (int loop = 0; loop < fsUPD.length; loop++) {
                        if (fsUPD[loop].getName().equals(stringBuilderUPD.toString())) {
                            checkFileUPD = true;
                            break;
                        }
                    }
                    if (!checkFileUPD) {
                        System.out.println("Incorrect syntax for UPD (Cannot find the file)");
                        break;
                    }
                    pathUPD = pathUPD + '/' + stringBuilderUPD.toString();

                    sendMessage(message.getMessage(UPD, CTS, username, content));
                    if (message.getStatus(getData(packet)) == SRF) {
                        System.out.println(message.getContent(getData(packet)));
                        break;
                    }

                    int TCPPort = Integer.parseInt(message.getContent(getData(packet)));

                    Socket socket = new Socket(serverHost, TCPPort);
                    BufferedInputStream bufferedInputStream = new BufferedInputStream(new FileInputStream(pathUPD));
                    byte[] bytes = new byte[MAX_FILE_SIZE];
                    int length;
                    OutputStream outputStream = socket.getOutputStream();
                    BufferedOutputStream bufferedOutputStream = new BufferedOutputStream(outputStream);
                    while ((length = bufferedInputStream.read(bytes)) != -1)
                        bufferedOutputStream.write(bytes, 0,length);
                    bufferedOutputStream.flush();
                    socket.shutdownOutput();
                    InputStream inputStream = socket.getInputStream();
                    byte[] serverBack = new byte[1024];
                    System.out.println(new String(serverBack, 0, inputStream.read(serverBack)));

                    socket.close();
                    bufferedInputStream.close();


                    break;

                case DWN:
                    if (content == null) {
                        System.out.println("Incorrect syntax for DWN (Loss Thread and Message)");
                        break;
                    }
                    int loopDWN = 0;
                    for (; loopDWN < content.length() && content.charAt(loopDWN) != ' '; loopDWN++);
                    if (loopDWN == content.length() || loopDWN == content.length() - 1) {
                        System.out.println("Incorrect syntax for DWN (Loss Message)");
                        break;
                    }
                    boolean checkDWN = true;
                    StringBuilder stringBuilderDWN = new StringBuilder();
                    for (loopDWN++; loopDWN < content.length(); loopDWN++) {
                        if (content.charAt(loopDWN) == ' ' && loopDWN != content.length() - 1) {
                            checkDWN = false;
                            System.out.println("Incorrect syntax for UPD (Input more argument)");
                            break;
                        }
                        stringBuilderDWN.append(content.charAt(loopDWN));
                    }
                    if (!checkDWN) break;

                    String pathDWN = new File("").getAbsolutePath() + "/src/Client/Resource/Download";
                    String downloadFile = stringBuilderDWN.toString();
                    File[] fsDWN = new File(pathDWN).listFiles();
                    boolean checkFileDWN = false;
                    for (int loop = 0; loop < fsDWN.length; loop++) {
                        if (fsDWN[loop].getName().equals(downloadFile)) {
                            checkFileDWN = true;
                            break;
                        }
                    }
                    if (checkFileDWN) {
                        System.out.println("Incorrect syntax for DWN (the file is existed)");
                        break;
                    }

                    sendMessage(message.getMessage(DWN, CTS, username, content));
                    if (message.getStatus(getData(packet)) == SRF) {
                        System.out.println(message.getContent(getData(packet)));
                        break;
                    }
                    ServerSocket TCPServerSocket = new ServerSocket(0);
                    sendMessage(message.getMessage(DWN, CTS, username,
                            Integer.toString(TCPServerSocket.getLocalPort())));

                    Socket TCPSocket = TCPServerSocket.accept();
                    InputStream DWNInputStream = TCPSocket.getInputStream();
                    BufferedInputStream DWNBufferedInputStream = new BufferedInputStream(DWNInputStream);

                    FileOutputStream DWNFileOutputStream = new FileOutputStream(pathDWN + '/' + downloadFile);
                    BufferedOutputStream DWNBufferedOutputStream = new BufferedOutputStream(DWNFileOutputStream);

                    byte[] DWNBytes = new byte[MAX_FILE_SIZE];
                    int DWNLength;
                    while ((DWNLength = DWNBufferedInputStream.read(DWNBytes)) != -1)
                        DWNBufferedOutputStream.write(DWNBytes, 0,DWNLength);
                    DWNBufferedOutputStream.flush();

                    OutputStream out = TCPSocket.getOutputStream();
                    String feedbackMessage = "Success";
                    out.write(feedbackMessage.getBytes());
                    DWNFileOutputStream.close();
                    TCPServerSocket.close();
                    TCPServerSocket.close();
                    System.out.println(downloadFile + " successfully downloaded");
                    break;

                case RMV:
                    if (content == null) {
                        System.out.println("Incorrect syntax for RMV");
                        break;
                    }
                    boolean checkRMV = true;
                    for (int loop = 0; loop < content.length(); loop++) {
                        if (content.charAt(loop) == ' ' && loop != content.length() - 1) {
                            System.out.println("Incorrect syntax for RMV");
                            checkRMV = false;
                            break;
                        }
                    }
                    if (!checkRMV) break;

                    sendMessage(message.getMessage(RMV, CTS, username, content));
                    System.out.println(message.getContent(getData(packet)));
                    break;


                case XIT:
                    sendMessage(message.getMessage(XIT, CTS, username, "exited"));
                    System.out.println("Goodbye");
                    System.exit(0);
                    break;


                default:
                    System.out.println("Invalid command");
                    break;
            }
        }
    }

    private static void sendMessage(String sendContent) throws Exception {
        byte[] content = sendContent.getBytes();
        boolean checkReceive = false;
        int loop = 10;

        for (; !checkReceive && loop > 0; loop--) {
            socket.send(new DatagramPacket(content, content.length, serverHost, serverPort));

            int checkConnect = 10;
            for (; checkConnect > 0; checkConnect--) {
                try {
                    packet = new DatagramPacket(new byte[MAX_SIZE], MAX_SIZE);
                    socket.receive(packet);
                } catch (Exception e) {
                    continue;
                }
                break;
            }
            if (checkConnect <= 0) {
                System.err.println("Server cannot connect!");
                System.exit(0);
            }

            if (message.getAction(getData(packet)) == message.getAction(sendContent)) {
                checkReceive = true;
            }

            if (message.getStatus(getData(packet)) == NGI) {
                System.err.println("The server may restart, the client closed");
                System.exit(0);
            }
        }

        if (loop <= 0) {
            System.err.println("Server do not receive correct message!");
            System.exit(0);
        }
    }

    private static String getData(DatagramPacket datagramPacket) throws Exception {
        byte[] buf = datagramPacket.getData();
        ByteArrayInputStream bais = new ByteArrayInputStream(buf);
        InputStreamReader isr = new InputStreamReader(bais);
        BufferedReader br = new BufferedReader(isr);
        return br.readLine();
    }

    private static int StringtoInt(String content) {
        StringBuilder actionString = new StringBuilder();
        for (int loop = 0; loop < 3; loop++)
            actionString.append(content.charAt(loop));

        switch (actionString.toString()) {
            case "CRT": return 2;
            case "MSG": return 3;
            case "DLT": return 4;
            case "EDT": return 5;
            case "LST": return 6;
            case "RDT": return 7;
            case "UPD": return 8;
            case "DWN": return 9;
            case "RMV": return 10;
            case "XIT": return 11;
            default: return 0;
        }
    }

    public static String getInputInformation(String content) {
        if (content.length() <= 4) return null;
        StringBuilder stringBuilder = new StringBuilder();
        int check = 0;
        for (int loop = 3; loop < content.length() && content.charAt(loop) != '\n'; loop++) {
            if (content.charAt(loop) == ' ' && check == 0) {
                check++;
                continue;
            }
            stringBuilder.append(content.charAt(loop));
        }
        return stringBuilder.toString();

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
        MAX_FILE_SIZE = 102400,
        TIMEOUT = 600;
}


