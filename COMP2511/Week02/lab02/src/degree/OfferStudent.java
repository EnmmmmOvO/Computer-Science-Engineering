package degree;

public class OfferStudent {
    private int places;
    private int offer;
    private listNode start;
    private listNode end;
    private class listNode {
        double score;
        Students students;
        listNode next;

        listNode(double score, Students students) {
            this.score = score;
            this.students = students;
            this.next = null;
        }
    }

    public OfferStudent(int places) {
        offer = 0;
        this.places = places;
        start = null;
        end = null;
    }

    public Students checkScore(Students students) {
        listNode l = start;
        for (; l != null; l = l.next) {
            if (students.equals(l.students)) return null;
        }
        double score = students.getHighScore();
        listNode newNode = new listNode(score, students);
        if (offer < places) {
            if (start == null) {
                start = newNode;
                end = newNode;
            } else if (score < start.score) {
                newNode.next = start;
                start = newNode;
            } else if (score > end.score) {
                end.next = newNode;
                end = newNode;
            } else {
                listNode temp = start;
                for (; temp != end; temp = temp.next) {
                    if (score > temp.score && score < temp.next.score) {
                        newNode.next = temp.next;
                        temp.next = newNode;
                        break;
                    }
                }
            }
            offer++;
            return null;
        } else {
            if (score <= start.score) {
                students.removeOffer();
                return students;
            } else if (score >= end.score) {
                Students temp = start.students;
                start = start.next;
                end.next = newNode;
                end = newNode;
                temp.removeOffer();
                return temp;
            } else {
                listNode temp = start;
                for (; temp != end; temp = temp.next)
                    if (compare(temp, score, students)) break;
                newNode.next = temp.next;
                temp.next = newNode;
                Students deleteStudents = start.students;
                start = start.next;
                deleteStudents.removeOffer();
                return deleteStudents;
            }
        }
    }

    private boolean compare(listNode l, double score, Students students) {
        if (l.score <= score && l.next.score >= score) {
            if (l.score == score && l.next.score == score) {
                if (!(l.students.getName().compareTo(students.getName()) > 0 &&
                        l.next.students.getName().compareTo(students.getName()) < 0)) return false;
            } else if (l.score == score) {
                if (l.students.getName().compareTo(students.getName()) < 0) return false;
            } else if (l.next.score == score) {
                if (l.next.students.getName().compareTo(students.getName()) > 0) return false;
            }
            return true;
        }
        return false;
    }

    public int getOffer() {
        return offer;
    }

    public double getCutoff() {
        return start == null ? 0 : start.score >= 99.95 ? 99.95 : start.score;
    }

    public boolean getVacancies() {
        return offer != places;
    }
}
