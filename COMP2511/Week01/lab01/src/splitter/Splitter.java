package splitter;

import java.util.Scanner;

public class Splitter {

    public static void main(String[] args) {
        System.out.println("Enter a sentence specified by spaces only: ");
        // Add your code
        Scanner scanner = new Scanner(System.in);
        String line = scanner.nextLine();
        String[] splitter = line.split(" ");

        for (int loop = 0; loop < splitter.length; loop++) {
            System.out.println(splitter[loop]);
        }
    }
}
