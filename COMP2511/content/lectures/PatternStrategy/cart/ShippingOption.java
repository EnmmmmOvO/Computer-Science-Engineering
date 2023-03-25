package cart;
/** Demo file, it may not be correct and/or complete.  
 * Please watch the corresponding lecture(s) for more explanations.
 * @author ashesh
 */

import java.util.ArrayList;

public interface ShippingOption {

	double  calculateCharges(ArrayList<Item> list);

}
