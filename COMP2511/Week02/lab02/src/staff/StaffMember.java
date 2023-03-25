package staff;

import java.util.Date;

public class StaffMember {
    private String name;
    private int salary;
    private Date hireDate;
    private Date endDate;

    public StaffMember(String name, int salary, Date hireDate, Date endDate) {
        this.endDate = endDate;
        this.hireDate = hireDate;
        this.salary = salary;
        this.name = name;
    }

    public String getName() {
        return name;
    }

    public Date getEndDate() {
        return endDate;
    }

    public Date getHireDate() {
        return hireDate;
    }

    public int getSalary() {
        return salary;
    }

    public void setEndDate(Date endDate) {
        this.endDate = endDate;
    }

    public void setHireDate(Date hireDate) {
        this.hireDate = hireDate;
    }

    public void setName(String name) {
        this.name = name;
    }

    public void setSalary(int salary) {
        this.salary = salary;
    }

    @Override
    public boolean equals(Object o) {
        if (o == null) return false;
        if (o == this) return true;

        if (o.getClass() != this.getClass()) return false;

        StaffMember s = (StaffMember) o;
        if (s.endDate.equals(endDate) && s.hireDate.equals(hireDate) && s.name.equals(name) && s.salary == salary) {
            return true;
        } else {
            return false;
        }
    }

    @Override
    public String toString() {
        return "name: " + name + " salary: " + salary + " hire date: " + hireDate + " end date: " + endDate;
    }
}

