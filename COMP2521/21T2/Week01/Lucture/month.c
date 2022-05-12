#include <stdio.h>
#include <string.h>
#include <assert.h>
#include <stdio.h>



char* monthName (int monthNumber) {
    switch (monthNumber) {
        case 1: return "Jan";
        case 2: return "Feb";
        case 3: return "Mar";
        case 4: return "Apr";
        case 5: return "May";
        case 6: return "Jun";
        case 7: return "Jul";
        case 8: return "Aug";
        case 9: return "Sep";
        case 10: return "Oct";
        case 11: return "Nov";
        case 12: return "Dec";
        default: return NULL;
    }
}

int main (int argc, char *argv[]) {
    assert (strcmp(monthName(1), "Jan") == 0);
}