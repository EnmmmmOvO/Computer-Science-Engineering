/*
 * Java multi-threading server with TCP
 * There are two points of this example code:
 * - socket programming with TCP e.g., how to define a server socket, how to exchange data between client and server
 * - multi-threading
 *
 * Author: Wei Song
 * Date: 2021-09-28
 * */

import java.net.*;
import java.io.*;

public class TCPServer {

    // Server information
    private static ServerSocket serverSocket;
    private static Integer serverPort;

    // define ClientThread for handling multi-threading issue
    // ClientThread needs to extend Thread and override run() method
    private static class ClientThread extends Thread {
        private final Socket clientSocket;
        private boolean clientAlive = false;

        ClientThread(Socket clientSocket) {
            this.clientSocket = clientSocket;
        }

        @Override
        public void run() {
            super.run();
            // get client Internet Address and port number
            String clientAddress = clientSocket.getInetAddress().getHostAddress();
            int clientPort = clientSocket.getPort();
            String clientID = "("+ clientAddress + ", " + clientPort + ")";

            System.out.println("===== New connection created for user - " + clientID);
            clientAlive = true;

            // define the dataInputStream to get message (input) from client
            // DataInputStream - used to acquire input from client
            // DataOutputStream - used to send data to client
            DataInputStream dataInputStream = null;
            DataOutputStream dataOutputStream = null;
            try {
                dataInputStream = new DataInputStream(this.clientSocket.getInputStream());
                dataOutputStream = new DataOutputStream(this.clientSocket.getOutputStream());
            } catch (IOException e) {
                e.printStackTrace();
            }

            while (clientAlive) {
                try {
                    // get input from client
                    // socket like a door/pipe which connects client and server together
                    // data from client would be read from clientSocket
                    assert dataInputStream != null;
                    assert dataOutputStream != null;
                    String message = (String) dataInputStream.readUTF();

                    if (message.equals("login")) {
                        System.out.println("[recv] login request from user - " + clientID);

                        // make corresponding response i.e., require user to provide username and password for further authentication
                        // dataOutputStream would be used to send the data to client side
                        String responseMessage = "You need to provide credentials";
                        System.out.println("[send] " + responseMessage);
                        dataOutputStream.writeUTF(responseMessage);
                        // finally call flush() which would flush all data to client side
                        dataOutputStream.flush();
                    } else if (message.equals("download")) {
                        System.out.println("[recv] download request from user - " + clientID);

                        // make corresponding response
                        String responseMessage = "You need to provide the file name you want to download";
                        System.out.println("[send] " + responseMessage);
                        dataOutputStream.writeUTF(responseMessage);
                        dataOutputStream.flush();
                    } else {
                        System.out.println("[recv]  " + message + " from user - " + clientID);
                        String responseMessage = "unknown request";
                        System.out.println("[send] " + message);
                        dataOutputStream.writeUTF(responseMessage);
                        dataOutputStream.flush();
                    }
                } catch (EOFException e) {
                    System.out.println("===== the user disconnected, user - " + clientID);
                    clientAlive = false;
                } catch (IOException e) {
                    e.printStackTrace();
                }
            }
        }
    }


    public static void main(String[] args) throws IOException {
        if (args.length != 1) {
            System.out.println("===== Error usage: java TCPServer SERVER_PORT =====");
            return;
        }

        // acquire port number from command line parameter
        serverPort = Integer.parseInt(args[0]);

        // define server socket with the input port number, by default the host would be localhost i.e., 127.0.0.1
        serverSocket = new ServerSocket(serverPort);
        // make serverSocket listen connection request from clients
        System.out.println("===== Server is running =====");
        System.out.println("===== Waiting for connection request from clients...=====");

        while (true) {
            // when new connection request reaches the server, then server socket establishes connection
            Socket clientSocket = serverSocket.accept();
            // for each user there would be one thread, all the request/response for that user would be processed in that thread
            // different users will be working in different thread which is multi-threading (i.e., concurrent)
            ClientThread clientThread = new ClientThread(clientSocket);
            clientThread.start();
        }
    }
}
