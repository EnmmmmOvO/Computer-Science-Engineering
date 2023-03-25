package headfirst.composite.menu;

import java.util.Iterator;
import java.util.ArrayList;

public class Menu extends MenuComponent {
	ArrayList<MenuComponent> menuComponents = new ArrayList<MenuComponent>();
	String name;
	String description;
  
	public Menu(String name, String description) {
		this.name = name;
		this.description = description;
	}
 
	public void add(MenuComponent menuComponent) {
		menuComponents.add(menuComponent);
	}
 
	public void remove(MenuComponent menuComponent) {
		menuComponents.remove(menuComponent);
	}
 
	public MenuComponent getChild(int i) {
		return (MenuComponent)menuComponents.get(i);
	}
 
	public String getName() {
		return name;
	}
 
	public String getDescription() {
		return description;
	}
 
	public void print() {
		System.out.print("\n" + getName());
		System.out.println(", " + getDescription());
		System.out.println("---------------------");
  
		Iterator<MenuComponent> iterator = menuComponents.iterator();
		while (iterator.hasNext()) {
			MenuComponent menuComponent = iterator.next();
			menuComponent.print();
		}
	}
	
	
	/**
	 * The following example is to illustrate an 
	 * alternative approach with a "constraint". 
	 * 
	 * Please note, there are better alternatives to 
	 * print Vegetarian items, like including the method 
	 * in the MenuComponent and its sub classes.  
	 */
	public void printVegetarianItems() {
		System.out.print("\n" + getName());
		System.out.println(", " + getDescription());
		System.out.println("---------------------");
  
		Iterator<MenuComponent> iterator = menuComponents.iterator();
		while (iterator.hasNext()) {
			MenuComponent menuComponent = iterator.next();
			
			if(menuComponent instanceof MenuItem) {
				if(menuComponent.isVegetarian()) {
					// Vegetarian ... ! 
					menuComponent.print();
				}
				else {
					//  NON vegetarian ... !  
				}
			}
			else if(menuComponent instanceof Menu) {
				((Menu)menuComponent).printVegetarianItems();
			}

			
		}
	}
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
/**	
	public void printV() {
		System.out.print("\n" + getName());
		System.out.println(", " + getDescription());
		System.out.println("---------------------");
  
		Iterator iterator = menuComponents.iterator();
		while (iterator.hasNext()) {
			MenuComponent menuComponent = 
				(MenuComponent)iterator.next();
			
			//menuComponent.print();
			if(menuComponent instanceof MenuItem) {
				MenuItem item = (MenuItem) menuComponent;
				if(item.isVegetarian()){
					item.print();
				}
			}
			else {
				System.out.println(" in Else ...");
				menuComponent.print();
			}
					
		}
	}
*/	
}
