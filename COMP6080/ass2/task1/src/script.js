/*
 *  COMP6080 23T3 -- Assignment 2 -- Funform
 *
 *  https://nw-syd-gitlab.cseunsw.tech/COMP6080/23T3/students/z5286124/funform
 *
 *  Written by Jinghan Wang (z5286124) on 02-10-2023.
 *
 */

const buildingType = document.getElementById('building-type');
const dob = document.getElementById('dob');
const postcode = document.getElementById('postcode');
const reset = document.getElementById('reset-form');
const result = document.getElementById('form-result')
const selectButton = document.getElementById('select-all-btn');
const streetName = document.getElementById('street-name');
const suburb = document.getElementById('suburb');

const featureList = [
    document.getElementById('features-heating'),
    document.getElementById('features-airconditioning'),
    document.getElementById('features-pool'),
    document.getElementById('features-sandpit')
];

let err = [true, true, true, true];
let selectStatus = false;

/*
 * Calculate Age:
 *
 *     - It computes the age as the difference in years between the current date and the birth date.
 *
 *     - If the current date is before the birth date within the same year, it decrements the age by 1.
 *
 */

const calculateAge = () => {
    const parts = dob.value.match(/^([0-9]{2})\/([0-9]{2})\/([0-9]{4})$/);
    const birthDate = new Date(parseInt(parts[3]), parts[2] - 1, parseInt(parts[1]));
    const currentDate = new Date();
    let age = currentDate.getFullYear() - birthDate.getFullYear();
    const monthDiff = currentDate.getMonth() - birthDate.getMonth();
    if (monthDiff < 0 || (monthDiff === 0 && currentDate.getDate() < birthDate.getDate())) {
        age--;
    }
    return age;
}

/*
 *  Features Output Sentence:
 *
 *      - If no features are selected, [features] is "no features"
 *
 *      - If 1 feature is selected, [features] is just "[feature1]"
 *
 *      - If 2 or more feature are selected, [features] is just "[feature1], [feature2], and [feature3]" etc, where
 *        "and" joins the last and second last feature.
 *
 */

const featureSentence = () => {
    let selectFeature = [];
    featureList.forEach(checkbox => {
        if (checkbox.checked) selectFeature.push(checkbox.value);
    });
    switch (selectFeature.length) {
        case 0: return 'no features';
        case 1: return selectFeature[0];
        default: return `${selectFeature.slice(0, -1).join(', ')}, and ${selectFeature.slice(-1)}`;
    }
}

const formResultUpdate = () => {

    /*
     *  If an error exists, the error is displayed in the following order of priority
     *
     *      1. Street: If they haven't inputted a street name, or the street name entered is invalid,
     *         the output should be "Please input a valid street name"
     *
     *      2. Suburb: If they have inputted a street name, but haven't inputted a suburb / the suburb
     *         is invalid, the output should be "Please input a valid suburb"
     *
     *      3. Postcode: If they have inputted a street name and suburb, but haven't inputted a
     *         postcode / the postcode is invalid, the output should be "Please input a valid postcode"
     *
     *      4. DOB: If they have inputted a street name, suburb, and postcode, but haven't inputted a
     *         valid date of birth, the output should be "Please enter a valid date of birth"
     *
     */

    const errSentence = [
        'Please input a valid street name',
        'Please input a valid suburb',
        'Please input a valid postcode',
        'Please enter a valid date of birth'
    ];

    for (const i in err) {
        if (err[i]) {
            result.value = errSentence[i];
            return;
        }
    }

    /*
     *  If no errors exist, the output should be:
     *      "You are [age (integer)] years old, and your address is [street name] St, [suburb], [postcode],
     *       Australia. Your building is [a|an] [building type], and it has [features]"
     */

    result.value = `You are ${calculateAge()} years old, and your address is ${streetName.value} St, ${suburb.value},` +
        ` ${postcode.value}, Australia. Your building is ` +
        `${buildingType.value === 'house' ? 'a House' : 'an Apartment'} and it has ${featureSentence()}`
}


/*
 *  Street Name: Text input for Street Name (must be between 3 and 50 characters inclusive)
 */

streetName.addEventListener('blur', () => {
    err[0] = streetName.value.length < 3 || streetName.value.length > 50;
    formResultUpdate();
});


/*
 *  Suburb: Text input for Suburb (must be between 3 and 50 characters inclusive)
 */

suburb.addEventListener('blur', () => {
    err[1] = suburb.value.length < 3 || suburb.value.length > 50;
    formResultUpdate();
});

/*
 *  Postcode: Text input for Postcode (must be a number that is exactly 4 digits)
 */

postcode.addEventListener('blur', () => {
    err[2] = !RegExp('^[0-9]{4}$').test(postcode.value);
    formResultUpdate();
});


/*
 *  Date of birth:
 *      Text input for Date of birth (valid input is the exact format "DD/MM/YYYY" and must be a valid date.
 *      This means it must match the regex expression "[0-9]{2}/[0-9]{2}/[0-9]{4}" and when trying to parse
 *      it with the Javascript date object it does not return NaN).
 */

const isValidDate = (year, month, day) => {
    // Prevent js date from actively solving overflow problems similar to 33/33/2023, and also prevent users
    // from setting times after now.
    const date = new Date(year, month - 1, day);
    return date.getFullYear() === parseInt(year) && date.getMonth() === parseInt(month) - 1 &&
           date.getDate() === parseInt(day) && date.getTime() <= new Date().getTime();
}

dob.addEventListener('blur', () => {
    const parts = dob.value.match(/^([0-9]{2})\/([0-9]{2})\/([0-9]{4})$/);
    err[3] = parts ? !isValidDate(parts[3], parts[2], parts[1]) : true;
    formResultUpdate();
});

/*  Building Type: If changed, update the output sentence.  */

buildingType.addEventListener('change', () => formResultUpdate());

/*
 *  Features:
 *      Checkbox for features that the house has (Heating, AirConditioning, Pool, Sandpit).
 *      Button to select / deselect all.
 *      When the Select All button is clicked inside the features section, all 4 feature checkboxes are selected.
 *          - At any time when all 4 features are selected, the Select All button's text is changed to Deselect all.
 *            When this button is pressed in this state, all 4 of the feature checkboxes become unselected.
 */

selectButton.addEventListener('click', () => {
    featureList.forEach(checkbox => checkbox.checked = !selectStatus);
    selectButton.value = selectStatus ? 'Select All' : 'Deselect All';
    selectStatus = !selectStatus;
    formResultUpdate();
});

featureList.forEach(checkbox => {
    // The select button check status when the user change the selects of sandboxes.
    checkbox.addEventListener('change', () => {
        let check = true;
        featureList.forEach(checkbox => check = checkbox.checked && check);
        selectButton.value = check ? 'Deselect All' : 'Select All';
        selectStatus = check;
        formResultUpdate();
    });
});


/*
 *  When the reset button is clicked, the textarea has all of its text removed (i.e. it becomes blank again),
 *  and all of the form elements in the table are reset to their default state.
 */

reset.addEventListener('click', () => {
    err = [true, true, true, true];
    result.value = '';
    selectStatus = false;

    streetName.value = '';
    suburb.value = '';
    postcode.value = '';
    dob.value = '';

    buildingType.value = 'apartment';

    featureList.forEach(checkbox => checkbox.checked = false);
    selectButton.value = 'Select All';
});
