package example;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;

public class LambdaTests {

	public static void main(String[] args){

		MyFunctionInterfaceA f1 = (x, y) -> x + y ;

		MyFunctionInterfaceA f2 = (x, y) -> x - y + 200;

		MyFunctionInterfaceB f3 = (x, y) ->  x > y  ;	

		MyFunctionInterfaceC f4 = x -> { 
                                        double y = 1.5*x; 
                                        return y + 8.0; 
                                    }; 

		System.out.println( f1.myCompute(10, 20) ); // prints 30
		System.out.println( f2.myCompute(10, 20) ); // prints 190
		System.out.println( f3.myCmp(10, 20) );     // prints false
		System.out.println( f4.doSomething(10) );   // prints 23.0

		Function<String, Integer> func = x -> x.length();
		Integer answer = func.apply("Sydney");   
		System.out.println(answer);  // prints 6

		Function<String, Integer> func1 = x -> x.length();
		Function<Integer, Boolean> func2 = x -> x > 5;
		Boolean result = func1.andThen(func2).apply("Sydney");  
		System.out.println(result);

		Predicate<Integer> myPass = mark -> mark >= 50 ; 
		List<Integer> listMarks = Arrays.asList(45, 50, 89, 65, 10);
		List<Integer> passMarks = listMarks.stream()
                				   .filter(myPass)
                				   .collect(Collectors.toList());

		System.out.println(passMarks); // prints [50, 89, 65] 

		Consumer<String> print = x -> System.out.println(x);
		print.accept("Sydney");   // prints Sydney

		// Consumer to multiply 5 to every integer of a list
		Consumer<List<Integer> > myModifyList = list ->  {
			for (int i = 0; i < list.size(); i++)
				list.set(i, 5 * list.get(i));
		};

		List<Integer> list = new ArrayList<Integer>();
		list.add(5);
		list.add(1);
		list.add(10);
	 
		// Implement myModifyList using accept()
		myModifyList.accept(list);

		// Consumer to display a list of numbers
		Consumer<List<Integer>> myDispList = myList -> {
			myList.stream().forEach(e -> System.out.println(e));
		};
		// Display list using myDispList
		myDispList.accept(list);

		List<String> strList = new ArrayList<String>();
		strList.add("Sydney");
		strList.add("");
		strList.add("Brisbane");
		strList.add("Perth");
		strList.add("");		
		strList.add("");	
		strList.add("Melbourne");			

		System.out.println("------- +++++++++++ ----------");

		Predicate<String> p = String::isEmpty; 

		// Collect empty strings 
		List<String> strEmptyList1 = strList.stream()
                				    .filter( p )
                				    .collect(Collectors.toList());
		
		System.out.println("Number of empty strings: " + strEmptyList1.size());
		// prints 3

		// Collect strings with length less than six
		List<String> strEmptyList2 = strList.stream()
                				    .filter( e -> e.length() < 6 )
                				    .collect(Collectors.toList());

		System.out.println("Number of strings with length < 6: " + strEmptyList2.size());
		// prints 4

		strList.stream().filter( e -> e.length() >= 6 ).forEach(e -> System.out.println(e));
		/** prints
		Sydney
		Brisbane
		Melbourne
		 */

		double avgNonEmptyStrLen = strList.stream()
						.filter( e -> e.length() > 0 )
						.mapToInt(String::length)
						.average()
						.getAsDouble();

		System.out.println("avgNonEmptyStrLen: " + avgNonEmptyStrLen);

		/** prints
		7.0
		 */ 
	}
}
