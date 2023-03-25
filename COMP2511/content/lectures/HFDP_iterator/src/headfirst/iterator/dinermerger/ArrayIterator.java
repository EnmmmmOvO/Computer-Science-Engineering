package headfirst.iterator.dinermerger;

public class ArrayIterator<T> implements Iterator<T> {
	T[] items;
	int position = 0;
 
	public ArrayIterator(T[] items) {
		this.items = items;
	}
 
	public T next() {
		T menuItem = items[position];
		position = position + 1;
		return menuItem;
	}
 
	public boolean hasNext() {
		if (position >= items.length || items[position] == null) {
			return false;
		} else {
			return true;
		}
	}
}
