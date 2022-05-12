
public class Message {
    public Message() {};

    public String getMessage(int action, int status, String name, String content) {
        return action + " " + status + " " + name + " " + content;
    }

    public int getAction(String message) {
        if (message.charAt(1) == ' ') {
            return message.charAt(0) - 48;
        } else {
            StringBuilder actionString = new StringBuilder();
            actionString.append(message.charAt(0));
            actionString.append(message.charAt(1));
            return Integer.parseInt(actionString.toString());
        }
    }

    public int getStatus(String message) {
        return getAction(message) >= 10 ? message.charAt(3) - 48  : message.charAt(2) - 48;
    }

    public String getName(String message) {
        int loop = getAction(message) >= 10 ? 5 : 4;
        StringBuilder stringBuilder = new StringBuilder();
        for (; message.charAt(loop) != ' '; loop++)
            stringBuilder.append(message.charAt(loop));
        return stringBuilder.toString();
    }

    public String getContent(String message) {
        int loop = 0;
        for (int temp = 0; temp < 3; loop++)
            if (message.charAt(loop) == ' ') temp++;


        StringBuilder content = new StringBuilder();
        for (; loop < message.length() && message.charAt(loop) != '\0'; loop++)
            content.append(message.charAt(loop));
        return content.toString();
    }

}
