// BFS maze solver

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "Cell.h"
#include "helpers.h"
#include "Maze.h"
#include "Queue.h"

bool solve(Maze m) {
    // TODO: Complete this function
    //       Feel free to add helper functions
    Cell start = MazeGetStart(m);
    int mazeHeight = MazeHeight(m);
    int mazeWidth = MazeWidth(m);
    bool **matrix = createBoolMatrix(mazeHeight, mazeWidth);
    Cell **matrixCell = createCellMatrix(mazeHeight, mazeWidth);

    Queue q = QueueNew();
    QueueEnqueue(q, start);

    bool stop = 0;
    while (!stop && !QueueIsEmpty(q))  {
        Cell point = QueueDequeue(q);

        if (matrix[point.row][point.col]) continue;

        matrix[point.row][point.col] = 1;
        if (MazeVisit(m, point)) {
            while (point.col != start.col || point.row != start.row) {
                MazeMarkPath(m, point);
                point = matrixCell[point.row][point.col];
            }
            MazeMarkPath(m, start);
            stop = 1;
        } else {
            Cell *nextPoint = malloc(sizeof(Cell) * 4);
            // Up position
            nextPoint[0].row = point.row - 1;
            nextPoint[0].col = point.col;

            // Right position
            nextPoint[1].row = point.row;
            nextPoint[1].col = point.col + 1;

            // Down position
            nextPoint[2].row = point.row + 1;
            nextPoint[2].col = point.col;

            //Left position
            nextPoint[3].row = point.row;
            nextPoint[3].col = point.col - 1;

            for (int loop = 0; loop < 4; loop++) {
                Cell c = nextPoint[loop];
                if (c.row >= 0 && c.col >= 0 && c.row < mazeHeight && c.col < mazeWidth ) {
                    if (!MazeIsWall(m, c) && !matrix[c.row][c.col]) {
                        QueueEnqueue(q, c);
                        matrixCell[c.row][c.col] = point; 
                    }
                }
            }
            free(nextPoint);
        }
        
    }

    QueueFree(q);
    freeBoolMatrix(matrix);
    freeCellMatrix(matrixCell);
    return stop;
}

