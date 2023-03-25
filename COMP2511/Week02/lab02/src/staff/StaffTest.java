package staff;

import org.junit.jupiter.api.Test;

import java.text.SimpleDateFormat;

import static org.junit.jupiter.api.Assertions.*;

public class StaffTest {

    @Test
    public void test(){
        try {
            SimpleDateFormat sdf = new SimpleDateFormat("yyyy-mm-dd");
            Lecturer lecturer1 = new Lecturer("John Smith", 10000, sdf.parse("2022-01-01"),
                    sdf.parse("2022-12-31"), "CSE", "A");
            Lecturer lecturer2 = new Lecturer("John Smith", 10000, sdf.parse("2022-01-01"),
                    sdf.parse("2022-12-31"), "CSE", "A");
            Lecturer lecturer3 = lecturer1;
            Lecturer lecturer4 = new Lecturer("Avatar Peter", 10000, sdf.parse("2022-01-01"),
                    sdf.parse("2022-12-31"), "Law", "C");
            Lecturer lecturer5 = new Lecturer("Avatar Peter", 20000, sdf.parse("2022-01-01"),
                    sdf.parse("2022-12-31"), "Law", "B");

            assertTrue(lecturer1.equals(lecturer2));
            assertTrue(lecturer1.equals(lecturer3));
            assertFalse(lecturer1.equals(lecturer4));
            assertFalse(lecturer4.equals(lecturer5));

            assertEquals("John Smith", lecturer1.getName());
            assertEquals(10000, lecturer1.getSalary());
            assertEquals(sdf.parse("2022-01-01"), lecturer1.getHireDate());
            assertEquals("Avatar Peter", lecturer4.getName());
            assertEquals("Law", lecturer4.getSchool());
            assertEquals("C", lecturer4.getAcademicStatus());

            System.out.println(lecturer1);
            System.out.println(lecturer4);
        } catch (Exception e) {}

    }
}
