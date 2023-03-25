package wondrous;

import java.util.ArrayList;
import java.util.List;

public class Wondrous {

    private final int MY_MAGIC_NUMBER = 42;

    public List<Integer> wondrous(int start) {
        int current = start;
        List<Integer> sequence = new ArrayList<Integer>();

        while (current != 1) {
            sequence.add(current);
            if (current % 2 == 0) {
                current /= 2;
            } else {
                current = (current * 3) + 1;
            }
        }

        return sequence;
    }

}