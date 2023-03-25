package average;

public class Average {
    /**
     * Returns the average of an array of numbers
     * 
     * @param the array of integer numbers
     * @return the average of the numbers
     */
    public float computeAverage(int[] nums) {
        float result = 0;
        // Add your code
        for (int loop = 0; loop < nums.length; loop++) 
            result += nums[loop];
        return result / nums.length;
    }

    public static void main(String[] args) {
        // Add your code
        int[] arrayA = new int[]{1, 2, 3, 4, 5};

        Average a = new Average();
        System.out.println("The average of numbers in the input array:" + a.computeAverage(arrayA));

        int[] arrayB = new int[]{11, 55, 88, 99, 44};

        Average b = new Average();
        System.out.println("The average of numbers in the input array:" + b.computeAverage(arrayB));
    }
}
