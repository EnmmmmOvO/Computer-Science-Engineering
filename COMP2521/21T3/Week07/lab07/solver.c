// Main program that runs the maze solver

// !!! DO NOT MODIFY THIS FILE !!!

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

#include "Maze.h"
#include "solve.h"

static void usage(char *progname);

int main(int argc, char *argv[]) {
    if (argc != 2 && argc != 3) {
        usage(argv[0]);
        exit(EXIT_FAILURE);
    }

    FILE *fp = fopen(argv[1], "r");
    if (fp == NULL) {
        fprintf(stderr, "%s: error: could not open '%s' for reading\n",
                argv[0], argv[1]);
        exit(EXIT_FAILURE);
    }

    Maze m = MazeRead(fp);
    fclose(fp);
    if (m == NULL) {
        fprintf(stderr, "%s: error: failed to read maze\n", argv[0]);
        exit(EXIT_FAILURE);
    }

    if (argc == 3) {
        int pauseMs;

        switch (atoi(argv[2])) {
            case  1:  pauseMs = 1000; break;
            case  2:  pauseMs =  500; break;
            case  3:  pauseMs =  200; break;
            case  4:  pauseMs =  100; break;
            case  5:  pauseMs =   50; break;
            case  6:  pauseMs =   20; break;
            case  7:  pauseMs =   10; break;
            case  8:  pauseMs =    5; break;
            case  9:  pauseMs =    2; break;
            case 10:  pauseMs =    1; break;
            case 11:  pauseMs =    0; break;
            default:
                usage(argv[0]);
                exit(EXIT_FAILURE);
        }

        MazeSetDisplayPause(pauseMs);
    }

    bool result = solve(m);

    printf("\nThe exit was %s\n", result ? "found!" : "not found.");

    MazeFree(m);
}

static void usage(char *progname) {
    fprintf(stderr, "usage: %s <maze file> [speed (1-11)]\n", progname);
}

