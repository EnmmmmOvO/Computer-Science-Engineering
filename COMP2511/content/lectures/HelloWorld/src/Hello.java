import java.util.Scanner;

public class Hello {

    public static boolean isLeap(int year){

        return ( (year % 4 == 0) && (year % 100 != 0) || (year % 400 == 0));

    }

    public static void main(String[] args) {
        
        System.out.println("Hello World!");

        int counter = 0;
        for(String str : args){
            System.out.println(++counter + " :: " + str);
        }

        System.out.println(args.length);

        int year = 2000;

        System.out.println( "Is a leap year? " + year + " : " + isLeap(year));

        Scanner in = new Scanner(System.in);
        String str2 = in.next();
        
        System.out.println(" >>> " + str2.toUpperCase());
        in.close();



    }
    
}