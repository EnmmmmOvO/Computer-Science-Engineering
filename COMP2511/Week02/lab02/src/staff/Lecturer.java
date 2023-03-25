package staff;

import java.util.Date;

public class Lecturer extends StaffMember{

    private String school;
    private String academicStatus;

    public Lecturer(String name, int salary, Date hireDate, Date endDate, String school, String academicStatus) {
        super(name, salary, hireDate, endDate);
        this.school = school;
        this.academicStatus = academicStatus;
    }

    public String getAcademicStatus() {
        return academicStatus;
    }

    public String getSchool() {
        return school;
    }

    public void setSchool(String school) {
        this.school = school;
    }

    public void setAcademicStatus(String academicStatus) {
        this.academicStatus = academicStatus;
    }

    @Override
    public String toString() {
        String temp = null;
        switch (academicStatus) {
            case "A": temp = "Associate Lecturer"; break;
            case "B": temp = "Lecturer"; break;
            case "C": temp = "Senior Lecturer"; break;
            default: break;
        }
        return super.toString() + " school: " + school + " academic status: " + temp;
    }

    @Override
    public boolean equals(Object o) {
        if (o == null) return false;
        if (o == this) return true;

        if (o.getClass() != this.getClass()) return false;

        Lecturer s = (Lecturer) o;
        if (s.getEndDate().equals(super.getEndDate()) &&
            s.getHireDate().equals(super.getHireDate()) &&
            s.getName().equals(super.getName()) && s.getSalary() == super.getSalary() &&
            s.academicStatus.equals(academicStatus) && s.school.equals(school)) {
            return true;
        } else {
            return false;
        }
    }
}
