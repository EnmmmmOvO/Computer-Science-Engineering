
import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.net.Socket;


public class HttpServer extends Thread {

    private static final String ROOT = "/Users/enmmmmovo/Documents/Study/COMP3331/Week04/Lab03/WebServer/Source";
    private InputStream inputStream;
    private OutputStream outputStream;
    private static String CRLF = "\r\n";
    private static String type;

    public HttpServer(Socket socket) {
        try {
            inputStream = socket.getInputStream();
            outputStream = socket.getOutputStream();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    private String read() {
        BufferedReader reader = new BufferedReader(new InputStreamReader(inputStream));
        try {
            String readLine = reader.readLine();
            String[] split = readLine.split(" ");
            if (split.length != 3) {
                return null;
            }
            System.out.println(readLine);
            return split[1];
        } catch (IOException e) {
            e.printStackTrace();
        }
        return null;
    }

    private void changeType(String filePath) {
        if (filePath.endsWith(".gif")) {
            type = "image/gif";
        } else if (filePath.endsWith(".png")) {
            type = "image/png";
        } else if (filePath.endsWith(".html")) {
            type = "text/html";
        } else {
            type = "application/octet-stream";
        }
    }

    private void response(String filePath) {
        changeType(filePath);
        File file = new File(ROOT + filePath);
        if (file.exists()) {
            try {
                if (type == "text/html") {
                    BufferedReader reader = new BufferedReader(new FileReader(file));
                    StringBuffer stringBuffer = new StringBuffer();
                    String line = null;
                    while ((line = reader.readLine()) != null) {
                        stringBuffer.append(line).append(CRLF);
                    }
                    StringBuffer result = new StringBuffer();
                    result.append("HTTP/1.1 200 ok " + CRLF);
                    result.append("Content-Type: text/html " + CRLF);
                    result.append("Content-Length:" + file.length() + CRLF);
                    result.append(CRLF + stringBuffer.toString());
                    outputStream.write(result.toString().getBytes());
                    outputStream.flush();
                    outputStream.close();
                } else {
                    StringBuffer result = new StringBuffer();
                    result.append("HTTP/1.1 200 ok " + CRLF);
                    result.append("Content-Type: " + type + CRLF);
                    outputStream.write(result.toString().getBytes());
                    outputStream.flush();
                    outputStream.close();
                }
            } catch (Exception e) {
                e.printStackTrace();
            }


        } else {
            StringBuffer error = new StringBuffer();
            error.append("HTTP/1.1 HTTP/1.1 404 NOT FOUND " + CRLF);
            error.append("Content-Type:text/html " + CRLF);
            error.append("Content-Length:19 " + CRLF).append(CRLF);
            error.append("<h1>404 Not Found..</h1>");
            try {
                outputStream.write(error.toString().getBytes());
                outputStream.flush();
                outputStream.close();
            } catch (IOException e) {
                e.printStackTrace();
            }
        }

    }

    public void HttpServerStart() {
        String filePath = read();
        response(filePath);
    }


}