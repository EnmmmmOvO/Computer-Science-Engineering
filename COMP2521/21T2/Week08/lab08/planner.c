// Algorithms to design electrical grids

#include <math.h>
#include <stdio.h>
#include <stdlib.h>

#include "Graph.h"
#include "Place.h"
#include "PQ.h"

////////////////////////////////////////////////////////////////////////
// Your task

double distance(Place p, Place q);

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
    // create a new graph to store all of the connection of cities and powerPlant
    Graph g = GraphNew(numCities + 1);

    for (int i = 0; i < numCities; i++) {
        // store the distance between two cities into Graph
        for (int j = i + 1; j < numCities; j++) {
            Edge f;
            f.v = i;
            f.w = j;
            // call the function to get the distance betweeen two cities
            f.weight = distance(cities[i], cities[j]);
            GraphInsertEdge(g, f);
        }
        // store the distance between a cities and powerPlant into Graph
        Edge e;
        e.v = i;
        e.w = numCities;
        // call the function to get the distance betweeen powerPlant and city
        e.weight = distance(cities[i], powerPlant);
        GraphInsertEdge(g, e);
    }

    //use Task1's sollution to get the cheapest way and made a new graph
    Graph newGraph = GraphMST(g);

    //Put the cheapest solution into powerLines and count the number of the powerline
    int number = 0;
    for (int i = 0; i < numCities; i++) {
        for (int j = i + 1; j < numCities; j++) {
            // store the detail between two cities into array
            if (GraphIsAdjacent(newGraph, i , j) > 0) {
                PowerLine temp1;
                temp1.p1 = cities[i];
                temp1.p2 = cities[j];
                powerLines[number] = temp1;
                number++; 
            }
        }
        // store the detail of city and powerplant into array
        if (GraphIsAdjacent(newGraph, i , numCities)) {
            PowerLine temp2;
            temp2.p1 = cities[i];
            temp2.p2 = powerPlant;
            powerLines[number] = temp2; 
            number++;
        }
    }

    // free the graph
    GraphFree(g);
    GraphFree(newGraph);
    // return the large of the array
    return number;
}

double distance(Place p, Place q) {
    // create a function to count the distance. distance = sqrt((x2-x1)^2+(y2-y1)^2)
    return sqrt(pow(q.x - p.x, 2) + pow(q.y - p.y, 2));
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
