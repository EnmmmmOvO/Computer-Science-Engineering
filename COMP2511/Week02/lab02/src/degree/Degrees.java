package degree;

import org.json.JSONObject;

public class Degrees {
    private int code;
    private String name;
    private String institution;
    private boolean vacancies;
    private OfferStudent offerStudent;

    public Degrees(int code, String name, String institution, int places) {
        this.code = code;
        this.name = name;
        this.institution = institution;
        offerStudent = new OfferStudent(places);
    }

    public Students addStudent(Students students) {
        return offerStudent.checkScore(students);
    }

    public JSONObject toJSON() {
        JSONObject jsonObject = new JSONObject();
        jsonObject.put("code", code);
        jsonObject.put("name", name);
        jsonObject.put("institution", institution);
        jsonObject.put("cutoff", offerStudent.getCutoff() != 0 ? offerStudent.getCutoff() : "-");
        jsonObject.put("offers", offerStudent.getOffer());
        jsonObject.put("vacancies", offerStudent.getVacancies());
        return jsonObject;
    }

}
