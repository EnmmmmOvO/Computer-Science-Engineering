package rational;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

public class Rational {

    private boolean exist;
    private int a;
    private int b;
    private String NegPos;

    public Rational(int a, int b) {
        if (b == 0)
            exist = false;
        else {
            exist = true;
            NegPos = a < 0 ? "-" : "";
            this.a = a == 0 ? a : a / greatestCommonDivisor(a, b);
            this.b = a == 0 ? b : b / greatestCommonDivisor(a, b);
        }
    }

    private int greatestCommonDivisor(int a, int b) {
        a = Math.abs(a);
        b = Math.abs(b);
        if (a == b) return a;
        if (a > b) return greatestCommonDivisor(a - b, a);
        return greatestCommonDivisor(a, b - a);
    }

    private String findCorrect(int a, List<String> list) {
        String temp = Integer.toString(a < 0 ? a * -1 : a);
        StringBuilder stringBuilder = new StringBuilder();
        for (int loop = 0; loop < temp.length(); loop++) stringBuilder.append(list.get(temp.charAt(loop) - 48));
        return stringBuilder.toString();
    }

    public Rational add(Rational num) {
        return new Rational(num.b * this.a + num.a * this.b, num.b * this.b);
    }

    public Rational subtract(Rational num) {
        return new Rational(num.b * this.a - num.a * this.b, num.b * this.b);
    }

    public Rational multiply(Rational num) {
        return new Rational(num.a * this.a, num.b * this.b);
    }

    public Rational divide(Rational num) {
        return new Rational(num.b * this.a, num.a * this.b);
    }


    private final List<String> SUPER_NUMS = new ArrayList<String>(Arrays.asList(new String[] {"⁰", "¹", "²", "³", "⁴", "⁵", "⁶", "⁷", "⁸", "⁹"}));

    private final List<String> SUB_NUMS = new ArrayList<String>(Arrays.asList(new String[] {"₀", "₁", "₂", "₃", "₄", "₅", "₆", "₇", "₈", "₉"}));

    @Override
    public String toString() {
        if (!exist) return "null";
        if (a % b == 0) return NegPos + Integer.toString(a / b);
        if (a < b) return NegPos + findCorrect(a, SUPER_NUMS) + '/' + findCorrect(b, SUB_NUMS);
        if (a > b) return NegPos + (a / b) + findCorrect(a % b, SUPER_NUMS) + '/' + findCorrect(b, SUB_NUMS);
        return null;
    }
}