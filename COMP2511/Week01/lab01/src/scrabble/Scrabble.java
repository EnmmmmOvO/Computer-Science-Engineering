package scrabble;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class Scrabble {

    private static String word;

    private static List<String> dictionary = new ArrayList<String>(Arrays.asList("ab", "abe", "able", "ad", "ae",
            "ah", "al", "ale", "at", "ate", "ba", "bad", "be", "bead", "bed", "bra", "brad", "bread", "bred",
            "cabble", "cable", "ea", "eat", "eater", "ed", "ha", "hah", "hat", "hate", "hater", "hath", "he",
            "heat", "heater", "heath", "heather", "heathery", "het", "in", "io", "ion", "li", "lin", "lion", "on",
            "program", "ra", "rad", "re", "rea", "read", "red", "sa", "sat", "scabble", "scrabble", "se", "sea", "seat",
            "seathe", "set", "seth", "sh", "sha", "shat", "she", "shea", "sheat", "sheath", "sheathe", "sheather",
            "sheathery", "sheth", "st", "te"));

    public Scrabble(String word) {
        this.word = word;
    }

    private int countScore() {
        int score = 0;
        for(int i = 0; i < dictionary.size(); i++) {
            if (word.length() == 2 && dictionary.get(i).equals(word)) return 1;
            int check = 0;
            int position = 0;
            for (int j = 0; j < dictionary.get(i).length(); j++) {
                int temp = word.indexOf(Character.toString(dictionary.get(i).charAt(j)));
                if (temp < position) {
                    check = 1;
                    break;
                } else
                    position = temp;
            }
            if (check == 0) System.out.println(dictionary.get(i));
            score = check == 0 ? score + 1 : score;
        }
        return score < 2 ? 0 : score;
    }

    public int score() {
        return countScore();
    }

}
