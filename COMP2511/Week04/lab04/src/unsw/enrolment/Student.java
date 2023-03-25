package unsw.enrolment;

import java.util.ArrayList;
import java.util.List;

public class Student {

    private String zid;
    private ArrayList<Enrolment> enrolments = new ArrayList<Enrolment>();
    private String name;
    private int program;
    private String[] streams;

	public Student(String zid, String name, int program, String[] streams) {
        this.zid = zid;
        this.name = name;
        this.program = program;
        this.streams = streams;
    }

    public boolean isEnrolled(CourseOffering offering) {
        return enrolments.stream().
                anyMatch(enrolment -> enrolment.getOffering().equals(offering));
    }

    public void setGrade(Grade grade) {
        enrolments.stream().
                filter(enrolment -> enrolment.getOffering().equals(grade.getOffering())).
                forEach(enrolment -> enrolment.setGrade(grade));
    }

    public void addEnrolment(Enrolment enrolment) {
        enrolments.add(enrolment);
    }

    public List<Enrolment> getEnrolments() {
        return enrolments;
    }

    public int compare(Student s) {
        return this.program != s.program ? this.program - s.program :
                this.enrolments.size() != s.enrolments.size() ? this.enrolments.size() - s.enrolments.size() :
                        !this.name.equals(s.name) ? this.name.compareTo(s.name) :
                                this.zid.compareTo(s.zid);

    }

    public String getZid() {
        return zid;
    }
}
