package headfirst.iterator.dinermerger;

import java.util.ArrayList;

public class ArrayListIterator<T> implements Iterator<T> {
	ArrayList<T> items;
	int position = 0;
 
	public ArrayListIterator(ArrayList<T> items) {
		this.items = items;
	}
 
	public T next() {
		T object = items.get(position);
		position = position + 1;
		return object;
	}
 
	public boolean hasNext() {
		if (position >= items.size()) {
			return false;
		} else {
			return true;
		}
	}
}
