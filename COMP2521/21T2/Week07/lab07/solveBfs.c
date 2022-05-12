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
    int height = MazeHeight(m);
    int width = MazeWidth(m);

    bool **matrix = createBoolMatrix(height, width);

    Cell **c = createCellMatrix(height, width);
    Cell start = MazeGetStart(m);
    
    Queue q = QueueNew();    
    QueueEnqueue(q, start);

    int loop = 0;
    while (loop == 0 && QueueIsEmpty(q) != true) {
        Cell p = QueueDequeue(q);

        if (matrix[p.row][p.col] != true) {
            matrix[p.row][p.col] = 1;
            
            if (MazeVisit(m, p)) {
                Cell w = p;
                
                while (w.col != start.col && w.row != start.row) {
                    MazeMarkPath(m, w);
                    w = c[w.row][w.col];
                }

                MazeMarkPath(m, start);
                loop = 1;
            } else {
                Cell array[4];

                array[0].row = p.row - 1;
                array[0].col = p.col;     // up
                array[1].row = p.row;
                array[1].col = p.col + 1; // right
                array[2].row = p.row + 1;
                array[2].col = p.col;     //  down
                array[3].row = p.row;
                array[3].col = p.col - 1; // left

                for (int i = 0; i < 4; i++) {
                    Cell a = array[i];
                    if (a.row >= 0 && a.row < MazeHeight(m) && a.col >= 0 && a.col < MazeWidth(m)) {
                        if (MazeIsWall(m, a) != true && matrix[a.row][a.col] != true) {
                            QueueEnqueue(q, a);
                            c[a.row][a.col] = p;
                        }
                    }
                }
            }
        }
    }

    QueueFree(q);
    freeBoolMatrix(matrix);
    freeCellMatrix(c);
    return loop;
}