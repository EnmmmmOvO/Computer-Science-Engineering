// Main program to test GraphMST

// !!! DO NOT MODIFY THIS FILE !!!

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "Graph.h"

static Graph readGraph(void);
static void outputPlain(Graph g, Graph mst);
static void outputVisualiser(Graph g, Graph mst);
static int min(int a, int b);

int main(int argc, char *argv[]) {
    if (argc > 2 || (argc == 2 && strcmp(argv[1], "-v") != 0)) {
        fprintf(stderr, "Usage: %s [-v]\n", argv[0]);
        exit(EXIT_FAILURE);
    }

    Graph g = readGraph();
    Graph mst = GraphMST(g);

    if (argc == 1) {        
        outputPlain(g, mst);
    } else {
        outputVisualiser(g, mst);
    }

    if (mst != NULL) GraphFree(mst);
    GraphFree(g);
}

static Graph readGraph(void) {
    int nV;
    scanf("%d", &nV);

    Graph g = GraphNew(nV);

    int v, w;
    double weight;
    while (scanf("%d,%d,%lf", &v, &w, &weight) == 3) {
        GraphInsertEdge(g, (Edge){v, w, weight});
    }

    return g;
}

static void outputPlain(Graph g, Graph mst) {
    printf("Graph:\n");
    GraphShow(g);
    printf("\n");

    if (mst == NULL) {
        printf("The graph has no minimum spanning tree.\n");
    } else {
        printf("Minimum Spanning Tree:\n");
        GraphShow(mst);
    }
}

static void outputVisualiser(Graph g, Graph mst) {
    FILE *fp = stdout;

    fprintf(fp,
        "<html>\n"
        "<head>\n"
        "  <title>Minimum Spanning Tree</title>\n"
        "  <link rel=\"stylesheet\" href=\"./style.css\">\n"
        "</head>\n"
        "<body>\n"
        "  <h1>Minimum Spanning Tree</h1>\n"
        "  <p>The minimum spanning tree is highlighted in green (if it exists).</p>\n"
        "  <div id=\"cy\"></div>\n"
        "  <script src=\"https://cdnjs.cloudflare.com/ajax/libs/cytoscape/3.19.0/cytoscape.min.js\" integrity=\"sha512-TOWs340KHbJjY/a2SCtsUcXYBg7/xPX72NKpJ3VITogkHJTy2yMyoJE0pxJjumMGHCg46ud89KO5q1Toe3Aeaw==\" crossorigin=\"anonymous\"></script>\n"
        "  <script>\n"
        "    var elems = [\n"
    );

    int nV = GraphNumVertices(g);
    for (int v = 0; v < nV; v++) {
        fprintf(fp,
            "      "
            "{data: {id: '%d'}},\n", v
        );
    }
    
    int eid = 1;
    for (int v = 0; v < nV; v++) {
        for (int w = v + 1; w < nV; w++) {
            double weight = GraphIsAdjacent(g, v, w);
            if (weight != 0.0) {
                fprintf(fp,
                    "      "
                    "{data: {id: 'e%d', source: '%d', "
                    "target: '%d', weight: %lf}},\n",
                    eid++, v, w, weight
                );
            }
        }
    }

    if (mst != NULL) {
        nV = min(nV, GraphNumVertices(mst));
        for (int v = 0; v < nV; v++) {
            for (int w = v + 1; w < nV; w++) {
                double weight = GraphIsAdjacent(mst, v, w);
                if (weight != 0.0) {
                    fprintf(fp,
                        "      "
                        "{data: {id: 'e%d', source: '%d', "
                        "target: '%d'}, classes: ['mst']},\n",
                        eid++, v, w
                    );
                }
            }
        }
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

static int min(int a, int b) {
    return a < b ? a : b;
}

