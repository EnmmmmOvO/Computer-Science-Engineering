// Algorithms to design electrical grids

#include <math.h>
#include <stdio.h>
#include <stdlib.h>

#include "Graph.h"
#include "Place.h"
#include "PQ.h"

////////////////////////////////////////////////////////////////////////
// Your task

double distance(Place a, Place b) {
    return sqrt(pow(a.x - b.x, 2) + pow(a.y - b.y, 2));
}

/**
 * Designs  a minimal cost electrical grid that will deliver electricity
 * from a power plant to all the given cities. Power lines must be built
 * between cities or between a city and a power plant.  Cost is directly
 * proportional to the total length of power lines used.
 * Assumes  that  numCities  is at least 1 (numCities is the size of the
 * cities array).
 * Stores the power lines that need to be built in the given  powerLines
 * array, and returns the number of power lines stored. Assumes that the
 * powerLines array is large enough to store all required power lines.
 */
int planGrid1(Place cities[], int numCities, Place powerPlant,
              PowerLine powerLines[]) {
    // TODO: Complete this function
    Graph g = GraphNew(numCities + 1);
    for (int loopA = 0; loopA < numCities; loopA++) {
        for (int loopB = loopA + 1; loopB < numCities; loopB++) {
            Edge e;
            e.v = loopA;
            e.w = loopB;
            e.weight = distance(cities[loopA], cities[loopB]);
            GraphInsertEdge(g, e);
        }
        Edge e;
        e.v = loopA;
        e.w = numCities;
        e.weight = distance(cities[loopA], powerPlant);
        GraphInsertEdge(g, e);
    }

    Graph new = GraphMST(g);
    

    int num = 0;
    for (int loopA = 0; loopA < numCities; loopA++) {
        for (int loopB = loopA + 1; loopB < numCities; loopB++) {
            if (GraphIsAdjacent(new, loopA, loopB)) {
                PowerLine pl;
                pl.p1 = cities[loopA];
                pl.p2 = cities[loopB];
                powerLines[num] = pl;
                num++;
            }
        }
        if (GraphIsAdjacent(new, loopA, numCities)) {
            PowerLine pl;
            pl.p1 = cities[loopA];
            pl.p2 = powerPlant;
            powerLines[num] = pl;
            num++;
        }
    }

    GraphFree(g);
    GraphFree(new);
    return num;
}


////////////////////////////////////////////////////////////////////////
// Optional task

/**
 * Designs  a minimal cost electrical grid that will deliver electricity
 * to all the given cities.  Power lines must be built between cities or
 * between a city and a power plant.  Cost is directly  proportional  to
 * the  total  length of power lines used.  Assume that each power plant
 * generates enough electricity to supply all cities, so not  all  power
 * plants need to be used.
 * Assumes  that  numCities and numPowerPlants are at least 1 (numCities
 * and numPowerPlants are the sizes of the cities and powerPlants arrays
 * respectively).
 * Stores the power lines that need to be built in the given  powerLines
 * array, and returns the number of power lines stored. Assumes that the
 * powerLines array is large enough to store all required power lines.
 */
int planGrid2(Place cities[], int numCities,
              Place powerPlants[], int numPowerPlants,
              PowerLine powerLines[]) {
    // TODO: Complete this function
    return 0;
}
