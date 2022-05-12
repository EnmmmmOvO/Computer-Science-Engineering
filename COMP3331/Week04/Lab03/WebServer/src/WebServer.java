import java.net.ServerSocket;
import java.net.Socket;

public final class WebServer {

    private static int port;
    private static ServerSocket host;

    public static void main(String[] args) throws Exception {

        if (args.length != 1) {
            System.err.println("Required arguments: port");
            return;
        }
        port = Integer.parseInt(args[0]);
        if (!(port == 80 || port == 8080 || port > 1024)) {
            System.err.println("The specify port id not a non-standard");
            return;
        }

        host = new ServerSocket(port);
        while (true) {
            Socket socket = host.accept();
            new HttpServer(socket).HttpServerStart();
        }

    }
}