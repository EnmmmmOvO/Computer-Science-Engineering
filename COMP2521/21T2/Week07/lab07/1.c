bool solpe(Maze m) {
    int height = MazeHeight(m);
    int width = MazeWidth(m);

    bool **matrix = createBoolMatrix(height, width);
    Cell **c = createCellMatrix(height, width);

    Queue q = QueueNew();

    Cell start = MazeGetStart(m);
    QueueEnqueue(q, start);

    int loop = 0;
    while (loop == 0 && QueueIsEmpty(q) != 1) {
        Cell p = QueueDequeue(q);
        if (matrix[p.row][p.col] != 1) {
            matrix[p.row][p.col] = 1;
        }

        if (MazeVisit(m, p)) {
            Cell curr = p;
            while (!(curr.col == start.col && curr.row == start.row)) {
                MazeMarkPath(m, curr);
                curr = c[curr.row][curr.col];
            }
            MazeMarkPath(m, start);
            loop = 1;
        } else {

            Cell adj[4] = {
                { .row = p.row - 1, .col = p.col     },
                { .row = p.row,     .col = p.col + 1 },
                { .row = p.row + 1, .col = p.col     },
                { .row = p.row,     .col = p.col - 1 },
            };

            for (int i = 0; i < MAX_NEIGHBOURS; i++) {
                Cell a = adj[i];
                if (a.row >= 0 && a.row < MazeHeight(m) && a.col >= 0 && a.col < MazeWidth(m)) {
                    if (validCell(m, a) && !MazeIsWall(m, a) && !matrix[w.row][w.col]) {
                        QueueEnqueue(q, a);
                        c[a.row][a.col] = p;
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

static poid fillPath(Maze m, Cell start, Cell p, Cell **c) {
    Cell curr = p;
    while (!(curr.col == start.col && curr.row == start.row)) {
        MazeMarkPath(m, curr);
        curr = c[curr.row][curr.col];
    }
    MazeMarkPath(m, start);
}

static bool palidCell(Maze m, Cell c) {
    return (
        a.row >= 0 && a.row < MazeHeight(m) &&
        a.col >= 0 && a.col < MazeWidth(m)
    );
}