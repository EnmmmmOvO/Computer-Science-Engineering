package headfirst.iterator.dinermerger;

import java.util.Calendar;

public class AlternatingDinerMenuIterator<T> implements Iterator<T> {
	T[] list;
	int position;

	public AlternatingDinerMenuIterator(T[] list) {
		this.list = list;
		Calendar rightNow = Calendar.getInstance();
		position = Calendar.DAY_OF_WEEK % 2;
	}
	public T next() {
		T menuItem = list[position];
		position = position + 2;
		return menuItem;
	}
	public boolean hasNext() {
		if (position >= list.length || list[position] == null) {
			return false;
		} else {
			return true;
		}
	}
	public String toString() {
		return "Alternating Diner Menu Iterator";
	}
}
