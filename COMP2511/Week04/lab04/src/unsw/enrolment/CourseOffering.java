package unsw.enrolment;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.stream.Collectors;

import unsw.enrolment.exceptions.InvalidEnrolmentException;

public class CourseOffering extends Course {

    private Course course;
    private String term;
    private List<Enrolment> enrolments = new ArrayList<Enrolment>();

    public CourseOffering(Course course, String term) {
        super(course.getCourseCode(), course.getTitle());
        this.course = course;
        this.term = term;
        this.course.addOffering(this);
    }

    public Course getCourse() {
        return course;
    }

    public String getCourseCode() {
        return course.getCourseCode();
    }

    public List<Course> getCoursePrereqs() {
        return course.getPrereqs();
    }

    public String getTerm() {
        return term;
    }

    public Enrolment addEnrolment(Student student) throws InvalidEnrolmentException {
        if (!checkValidEnrolment(student))
            throw new InvalidEnrolmentException("student has not satisfied the prerequisites");

        Enrolment enrolment = new Enrolment(this, student);
        enrolments.add(enrolment);
        student.addEnrolment(enrolment);
        return enrolment;
    }

    private boolean checkValidEnrolment(Student student) {
        for (Course prereq : getCoursePrereqs()) {
            List<Enrolment> studentEnrolments = student.getEnrolments();
            boolean valid = false;

            for (Enrolment enrolment : studentEnrolments) {
                valid = enrolment.getCourse().equals(prereq) && enrolment.getGrade() != null
                        && enrolment.getGrade().getMark() >= 50 && enrolment.getGrade().getGrade() != "FL"
                        && enrolment.getGrade().getGrade() != "UF" || valid;

                if (!valid) return false;
            }
        }
        return true;
    }

    private static class ComparatorStudent implements Comparator<Student> {
        @Override
        public int compare(Student student1, Student student2) {
            return student1.compare(student2);
        }
    }

    public List<Student> studentsEnrolledInCourse(List<Student> students) {
        return students.stream().sorted(new ComparatorStudent()::compare).collect(Collectors.toList());
    }

}