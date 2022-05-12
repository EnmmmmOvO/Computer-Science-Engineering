
import java.net.*;
import java.util.Date;


public class PingClient {

    private static final int Timeout = 600;
    private static final int SendTime = 15;

    private static InetAddress Host;
    private static DatagramSocket socket;
    private static int Port;

    private static long AverageTime = 0;
    private static int SuccessTime = 0;
    private static long MaxTime = 0;
    private static long MinTime = Timeout;

    public static void main(String[] args) throws Exception {

        if (args.length != 2) {
            System.err.println("Required arguments: host, port");
            return;
        }

        // Transfer args[0] to InetAddress type;
        Host = InetAddress.getByName(args[0]);
        Port = Integer.parseInt(args[1]);

        socket = new DatagramSocket();
        // Set Timeout 600ms
        socket.setSoTimeout(Timeout);

        for (int loop = 0; loop < SendTime; loop++) {
            // Record the time when the packet send;
            long TimeSend = (new Date()).getTime();

            // PING 1 time(ms) \r\n
            byte[] SendMessage = new byte[100];
            SendMessage = ("PING " + loop + " " + TimeSend + " \r\n").getBytes();

            DatagramPacket receive = new DatagramPacket(new byte[100], 100);
            socket.send(new DatagramPacket(SendMessage, SendMessage.length, Host, Port));
            try {
                socket.receive(receive);

                Long Delay = (new Date()).getTime() - TimeSend;
                System.out.println("ping to " + Host.getHostAddress() + ", seq = " + loop + ", rtt = " + Delay + " ms");

                SuccessTime++;
                AverageTime += Delay;
                MaxTime = MaxTime > Delay ? MaxTime : Delay;
                MinTime = MinTime < Delay ? MinTime : Delay;

            } catch (Exception ex) {
                System.out.println("ping to " + Host.getHostAddress() + ", seq = " + loop + ", Time Out");
            }
        }

        System.out.println("\n--- ping localhost statistics ---");
        Double LossPercentage = Double.valueOf((SendTime - SuccessTime) * 100/ SendTime);
        System.out.println(SendTime + " packets transmitted, " + SuccessTime + " packets received, "
                + LossPercentage + "% packet loss");
        System.out.println("round trip min/avg/max = " + Double.valueOf(MinTime) + "/"
                + Double.valueOf(AverageTime / SuccessTime) + "/" + Double.valueOf(MaxTime) + " ms");
    }
}
