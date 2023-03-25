package example;

public class Square extends Rectangle {

	@Override
	public void setWidth(int aWidth) {
		super.setWidth(aWidth);
		super.setHeight(aWidth);
	}

	@Override
	public void setHeight(int aHeight) {
		super.setWidth(aHeight);
		super.setHeight(aHeight);
	}
	
}
