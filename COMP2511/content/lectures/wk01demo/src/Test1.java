public class Test1 {
    
    public static void main(String[] args) {
        
        Circle c1 = new Circle();

        System.out.println( "c1 area: "+ c1.getArea() );

        Circle c2 = new Circle(2, 5, 8);
        System.out.println( c2.getArea() );

        System.out.println( Circle.no_circles );

        System.out.println( c2 );

        Circle c3 = new Circle(2, 5, 8);

        c1 = c2;
        System.out.println("revised, c1 area: "+ c1.getArea() );

        System.out.println( c2 == c3 ); 
        System.out.println( c2.equals(c3) ); 



    }


}