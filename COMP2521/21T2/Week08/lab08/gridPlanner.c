
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "Place.h"
#include "planner.h"

#define MAX_CITIES       128
#define MAX_POWER_PLANTS  16

static void readPlaces(Place cities[], int *numCities,
                       Place powerPlants[], int *numPowerPlants);
static bool readPlace(Place *p, bool *isPowerPlant);
static void chomp(char *s);

static void outputPlain(Place cities[], int numCities,
                        Place powerPlants[], int numPowerPlants,
                        PowerLine powerLines[], int numPowerLines);
static void outputVisualiser(Place cities[], int numCities,
                             Place powerPlants[], int numPowerPlants,
                             PowerLine powerLines[], int numPowerLines);

int main(int argc, char *argv[]) {
    if (argc > 2 || (argc == 2 && strcmp(argv[1], "-v") != 0)) {
        fprintf(stderr, "Usage: %s [-v]\n", argv[0]);
        return EXIT_FAILURE;
    }

    Place cities[MAX_CITIES];
    int numCities = 0;

    Place powerPlants[MAX_POWER_PLANTS];
    int numPowerPlants = 0;

    readPlaces(cities, &numCities, powerPlants, &numPowerPlants);

    int numPlaces = numCities + numPowerPlants;
    PowerLine *powerLines = calloc((numPlaces * numPlaces),
                                   sizeof(PowerLine));

    int numPowerLines;
    if (numPowerPlants == 1) {
        numPowerLines = planGrid1(cities, numCities, powerPlants[0],
                                  powerLines);
    } else {
        // Optional task
        numPowerLines = planGrid2(cities, numCities, powerPlants,
                                  numPowerPlants, powerLines);
    }

    if (argc == 1) {
        outputPlain(cities, numCities, powerPlants, numPowerPlants,
                    powerLines, numPowerLines);
    } else {
        outputVisualiser(cities, numCities, powerPlants, numPowerPlants,
                         powerLines, numPowerLines);
    }

    free(powerLines);
}

static void readPlaces(Place cities[], int *numCities,
                       Place powerPlants[], int *numPowerPlants) {
    Place pl;
    bool isPowerPlant;
    while (readPlace(&pl, &isPowerPlant)) {
        if (isPowerPlant) {
            if (*numPowerPlants < MAX_POWER_PLANTS) {
                powerPlants[(*numPowerPlants)++] = pl;
            } else {
                fprintf(stderr, "warning: too many power plants, "
                        "ignoring %s\n", pl.name);
            }
        } else {
            if (*numCities < MAX_CITIES) {
                cities[(*numCities)++] = pl;
            } else {
                fprintf(stderr, "warning: too many cities, "
                        "ignoring %s\n", pl.name);
            }
        }
    }

    if (*numCities == 0) {
        fprintf(stderr, "error: no cities\n");
        exit(EXIT_FAILURE);
    } else if (*numPowerPlants == 0) {
        fprintf(stderr, "error: no power plants\n");
        exit(EXIT_FAILURE);
    }
}

static bool readPlace(Place *p, bool *isPowerPlant) {
    char *line = NULL;
    size_t n = 0;
    if (getline(&line, &n, stdin) < 0) {
        free(line);
        return false;
    }
    chomp(line);

    char type[6];
    bool success = false;
    char format[100];
    sprintf(format, "%%5[^,],%%%d[^,],%%d,%%d", MAX_PLACE_NAME);
    if (sscanf(line, format,
               type, p->name, &(p->x), &(p->y)) == 4) {
        if (strcmp(type, "city") == 0) {
            *isPowerPlant = false;
            success = true;
        } else if (strcmp(type, "plant") == 0) {
            *isPowerPlant = true;
            success = true;
        }
    }

    free(line);
    return success;
}

static void chomp(char *s) {
    int len = strlen(s);
    if (len != 0 && s[len - 1] == '\n') {
        s[len - 1] = '\0';
    }
}

////////////////////////////////////////////////////////////////////////

static void outputPlain(Place cities[], int numCities,
                        Place powerPlants[], int numPowerPlants,
                        PowerLine powerLines[], int numPowerLines) {
    for (int i = 0; i < numCities; i++) {
        printf("City %s at (%d, %d)\n",
               cities[i].name,
               cities[i].x, cities[i].y);
    }

    for (int i = 0; i < numPowerPlants; i++) {
        printf("Power Plant %s at (%d, %d)\n",
               powerPlants[i].name,
               powerPlants[i].x, powerPlants[i].y);
    }

    for (int i = 0; i < numPowerLines; i++) {
        PowerLine *l = &(powerLines[i]);
        printf("Power line between %s (%d, %d) and %s (%d, %d)\n",
               l->p1.name, l->p1.x, l->p1.y,
               l->p2.name, l->p2.x, l->p2.y);
    }
}

static void outputVisualiser(Place cities[], int numCities,
                             Place powerPlants[], int numPowerPlants,
                             PowerLine powerLines[], int numPowerLines) {
    FILE *fp = stdout;

    fprintf(fp,
        "<html>\n"
        "<head>\n"
        "  <title>Electrical Grid Plan</title>\n"
        "  <link rel=\"stylesheet\" href=\"./style.css\">\n"
        "</head>\n"
        "<body>\n"
        "  <h1>Electrical Grid Plan</h1>\n"
        "  <p>Power plants are coloured yellow.</p>\n"
        "  <div id=\"cy\"></div>\n"
        "  <script src=\"https://cdnjs.cloudflare.com/ajax/libs/cytoscape/3.19.0/cytoscape.min.js\" integrity=\"sha512-TOWs340KHbJjY/a2SCtsUcXYBg7/xPX72NKpJ3VITogkHJTy2yMyoJE0pxJjumMGHCg46ud89KO5q1Toe3Aeaw==\" crossorigin=\"anonymous\"></script>\n"
        "  <script>\n"
        "    var elems = [\n"
    );

    for (int i = 0; i < numCities; i++) {
        fprintf(fp,
            "      "
            "{data: {id: \"%s\"}, position: {x: %d, y: %d}},\n",
            cities[i].name, cities[i].x, -cities[i].y
        );
    }

    for (int i = 0; i < numPowerPlants; i++) {
        fprintf(fp,
            "      "
            "{data: {id: \"%s\"}, position: {x: %d, y: %d}, "
            "classes: ['power-plant']},\n",
            powerPlants[i].name, powerPlants[i].x, -powerPlants[i].y
        );
    }

    int eid = 1;
    for (int i = 0; i < numPowerLines; i++) {
        fprintf(fp,
            "      "
            "{data: {id: 'e%d', source: \"%s\", target: \"%s\"}},\n",
            eid++, powerLines[i].p1.name, powerLines[i].p2.name
        );
    }

    fprintf(fp,
        "    ];\n"
        "  </script>\n"
        "  <script src=\"./visualiser.js\"></script>\n"
        "</body>\n"
        "</html>\n"
    );

    // fclose(fp);
}

