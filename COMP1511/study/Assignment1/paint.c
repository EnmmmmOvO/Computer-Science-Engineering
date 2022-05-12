// Assignment 1 20T3 COMP1511: CS Paint
// paint.c
//
// This program was written by YOUR-NAME-HERE (z5555555)
// on INSERT-DATE-HERE
//
// Version 1.0.0 (2020-10-04): Assignment released.

#include <stdio.h>

// The dimensions of the canvas (20 rows x 36 columns).
#define N_ROWS 20
#define N_COLS 36

// Shades (assuming your terminal has a black background).
#define BLACK 0
#define DARK 1
#define GREY 2
#define LIGHT 3
#define WHITE 4

// IF YOU NEED MORE #defines ADD THEM HERE
void drawLine(int array[N_ROWS][N_COLS], int start_row, int start_col, int end_row, int end_col, int color);
void drawSquare(int array[N_ROWS][N_COLS], int start_row, int start_col, int end_row, int end_col, int color);
void copyOrpaste(int array[N_ROWS][N_COLS], int start_row, int start_col, int end_row, int end_col, int target_col, int target_row);
int check(int arrayA[N_ROWS][N_COLS], int arrayB[N_ROWS][N_COLS]);
void saveArray(int arrayA[N_ROWS][N_COLS], int arrayB[N_ROWS][N_COLS]);

// Provided helper functions:
// Display the canvas.
void displayCanvas(int canvas[N_ROWS][N_COLS]);
// Clear the canvas by setting every pixel to be white.
void clearCanvas(int canvas[N_ROWS][N_COLS]);


// ADD PROTOTYPES FOR YOUR FUNCTIONS HERE


int main(void) {
    int canvas[N_ROWS][N_COLS];
    int record[N_ROWS][5];
    clearCanvas(canvas);
    
    int line;
    //Stage Oneinput
    int start_row;
    int start_col;
    int end_row;
    int end_col;
    int color = 0; 
    int target_row;
    int target_col;
    int recordTime;
    int row_offset = 0;
    int col_offset = 0;
    int numberSeven = 0;
    int saveA[N_ROWS][N_COLS] = {0};
    int saveB[N_ROWS][N_COLS] = {0};
    int saveC[N_ROWS][N_COLS] = {0};
    int saveD[N_ROWS][N_COLS] = {0};
    int saveE[N_ROWS][N_COLS] = {0};
    while (scanf("%d", &line) == 1) 
    {
        if (line == 1 || line == 2) {
            scanf("%d", &start_row);
            scanf("%d", &start_col);
            scanf("%d", &end_row);
            scanf("%d", &end_col);
            if (line == 1)
            {
                drawLine(canvas, start_row, start_col, end_row, end_col, color);
            }
            if (line == 2)
            {
                drawSquare(canvas, start_row, start_col, end_row, end_col, color);
            }
        }
        if (line == 3) {
            int color_test;
            scanf("%d", &color_test);
            if (color_test <= 4 && color_test >= 0) {
                color = color_test;
            }
        }
        if (line == 4) {
            scanf("%d", &start_row);
            scanf("%d", &start_col);
            scanf("%d", &end_row);
            scanf("%d", &end_col);
            scanf("%d", &target_row);
            scanf("%d", &target_col);
            copyOrpaste(canvas, start_row, start_col, end_row, end_col, target_col, target_row);
        }
        if (line == 5) {
            scanf("%d", &recordTime);
            int loopRecordA = 0;
            while (loopRecordA < recordTime) {
                int loopRecordB = 0;
                while (loopRecordB < 5) {
                    scanf("%d", &record[loopRecordA][loopRecordB]);
                    loopRecordB ++;
                }
                loopRecordA ++;
            }
        }
        if (line == 6) {
            scanf("%d", &row_offset);
            scanf("%d", &col_offset);
            int loopRecordC = 0;
            while (loopRecordC < recordTime) {
                int recordLine = record[loopRecordC][0];
                int recordStartRow = record[loopRecordC][1] + row_offset;
                int recordStartCol = record[loopRecordC][2] + col_offset;
                int recordEndRow = record[loopRecordC][3] + row_offset;
                int recordEndCol = record[loopRecordC][4] + col_offset;
                if (recordLine == 1) {
                    drawLine(canvas, recordStartRow, recordStartCol, recordEndRow, recordEndCol, color);
                }
                if (recordLine == 2) {
                    drawSquare(canvas, recordStartRow, recordStartCol, recordEndRow, recordEndCol, color);
                }
                loopRecordC ++;
            }
        }
        if (line == 7) {
            if (numberSeven == 0) {
                if (check(saveA, canvas) == 1) {
                    numberSeven ++;
                    saveArray(saveA, canvas);

                }
            } else if (numberSeven == 1) {
                if (check(saveB, canvas) == 1) {
                    numberSeven ++;
                    saveArray(saveB, canvas);
                }
            } else if (numberSeven == 2) {
                if (check(saveC, canvas) == 1) {
                    numberSeven ++;
                    saveArray(saveC, canvas);
                }
            } else if (numberSeven == 3) {
                if (check(saveD, canvas) == 1) {
                    numberSeven ++;
                    saveArray(saveD, canvas);
                }
            } else if (numberSeven == 4) {
                if (check(saveE, canvas) == 1) {
                    numberSeven ++;
                    saveArray(saveE, canvas);
                }
            } else if (numberSeven == 5) {
                if (check(saveA, canvas) == 1) {
                    saveArray(saveA, saveB);
                    saveArray(saveB, saveC);
                    saveArray(saveC, saveD);
                    saveArray(saveD, saveE);
                    saveArray(saveE, canvas);
                }
            }

            
        }
    }
    if (numberSeven == 1) {
        displayCanvas(saveA);
        printf("\n");
    }
    if (numberSeven == 2) {
        displayCanvas(saveA);
        printf("\n");
        displayCanvas(saveB);
        printf("\n");
    }
    if (numberSeven == 3) {
        displayCanvas(saveA);
        printf("\n");
        displayCanvas(saveB);
        printf("\n");
        displayCanvas(saveC);
        printf("\n");
    }
    if (numberSeven == 4) {
        displayCanvas(saveA);
        printf("\n");
        displayCanvas(saveB);
        printf("\n");
        displayCanvas(saveC);
        printf("\n");
        displayCanvas(saveD);
        printf("\n");
    }
    if (numberSeven == 5) {
        displayCanvas(saveA);
        printf("\n");
        displayCanvas(saveB);
        printf("\n");
        displayCanvas(saveC);
        printf("\n");
        displayCanvas(saveD);
        printf("\n");
        displayCanvas(saveE);
        printf("\n");
    }

    // TODO: Add your code here!

    // Hint: start by scanning in the command.
    //
    // If the command is the "Draw Line" command, scan in the rest of
    // the command (start row, start col, length, direction) and use
    // that information to draw a line on the canvas.
    //
    // Once your program can draw a line, add a loop to keep scanning
    // commands until you reach the end of input, and process each
    // command as you scan it.

    displayCanvas(canvas);

    return 0;
}


void drawLine(int array[N_ROWS][N_COLS], int start_row, int start_col, int end_row, int end_col, int color) {
    if (start_row < 0 || start_col < 0 || start_row > 20 || start_col > 36){
        if (end_row < 0 || end_col < 0 || end_row > 20 || end_col > 36)
        {
            return;
        }
    }

    //Line
    if (start_row == end_row || start_col == end_col) {
        if (start_row > end_row) {
            int midA = start_row;
            start_row = end_row;
            end_row = midA;
        }
        if (start_col > end_col) {
            int midB = start_col;
            start_col = end_col;
            end_col = midB;
        }

        if (end_row > 20) {
            end_row = 19;
        }
        if (start_row < 0) {
            start_row = 0;
        }
        if (end_col > 36) {
            end_col = 35;
        }
        if (start_col < 0) {
            start_col = 0;
        }

        if (start_row == end_row) {
            int loopStart = start_col;
            while (loopStart <= end_col)
            {
                array[start_row][loopStart] = color;
                loopStart ++;
            }
            return;
        } else if (start_col == end_col) {
            int loopStart = start_row;
            while (loopStart <= end_row)
            {
                array[loopStart][start_col] = color;
                loopStart ++;
            }  
            return;
        }
    }

    //Diagonals
    if (start_col - end_col == start_row - end_row) {
        if (start_col + start_row > end_row + end_col) {
            int midA = start_col;
            int midB = start_row;
            start_col = end_col;
            start_row = end_row;
            end_col = midA;
            end_row = midB;
        }
        int loopStartCol = start_col;
        int loopStartRow = start_row;
        if (loopStartRow < 0 || loopStartCol < 0) {
            loopStartRow ++;
            loopStartCol ++;
        }
        if (end_col < 36 && end_row < 20) {
            int loopStart = loopStartCol < loopStartRow ? loopStartCol : loopStartRow;
            int loopEnd = loopStart == loopStartCol ? end_col : end_row;
            while(loopStart <= loopEnd) {
                array[loopStartRow][loopStartCol] = color;

                loopStartCol ++;
                loopStartRow ++;
                loopStart ++;
            }
        } else {
            int loop = 0;
            while (loop == 0)
            {
                array[loopStartRow][loopStartCol] = color;
                loopStartCol ++;
                loopStartRow ++;
                if (loopStartCol >= 36 || loopStartRow >= 20)
                {
                    loop = 1;
                }
            }
        }
    } else if (start_col - end_col == end_row - start_row) {
        int loopStartCol = start_col;
        int loopStartRow = start_row;
        int loopEndRow = end_row;
        int loopEndCol = end_col;
        if (end_col >= 0 && end_col < 36 && end_row >= 0 && end_row < 20) {
            loopStartCol = end_col;
            loopStartRow = end_row;
            loopEndRow = start_row;
            loopEndCol = start_col;
        }

        int loop = 0;
        if (loopStartRow > loopEndRow)
        {
            while (loop == 0) {
                array[loopStartRow][loopStartCol] = color;
                loopStartRow --;
                loopStartCol ++;
                if (loopStartRow < loopEndRow || loopStartCol > loopEndCol) {
                    loop = 1;
                }
                if (loopStartRow < 0 || loopStartRow >= 20 || loopStartCol < 0 || loopStartCol >= 36) {
                    loop = 1;
                }
            }
        } else {
            while (loop == 0) {
                array[loopStartRow][loopStartCol] = color;
                loopStartRow ++;
                loopStartCol --;
                if (loopStartRow > loopEndRow || loopStartCol < loopEndCol) {
                    loop = 1;
                }
                if (loopStartRow < 0 || loopStartRow >= 20 || loopStartCol < 0 || loopStartCol >= 36) {
                    loop = 1;
                }
            }
        }
    }
}

void drawSquare(int array[N_ROWS][N_COLS], int start_row, int start_col, int end_row, int end_col, int color) {
    if (start_row < 0 || start_col < 0)
    {
        if (end_row > 20 || end_col > 36)
        {
            return;
        }
    }
    if (start_row > end_row)
    {
        int midA = start_row;
        start_row = end_row;
        end_row = midA;
    }
    if (start_col > end_col)
    {
        int midB = start_col;
        start_col = end_col;
        end_col = midB;
    }
    if (end_row > 20)
    {
        end_row = 19;
    }
    if (start_row < 0) 
    {
        start_row = 0;
    }
    if (end_col > 36)
    {
        end_col = 35;
    }
    if (start_col < 0) 
    {
        start_col = 0;
    }

    
    int loopRow = start_row;
    while (loopRow <= end_row)
    {
        int loopCol = start_col;
        while (loopCol <= end_col)
        {
            array[loopRow][loopCol] = color;
            loopCol ++;
        }
        loopRow ++;
    }

}

void copyOrpaste(int array[N_ROWS][N_COLS], int start_row, int start_col, int end_row, int end_col, int target_col, int target_row) {
    int array1[N_ROWS][N_COLS] = {0};
    int loopRow = 0;
    while (loopRow < N_ROWS) {
        int loopCol = 0;
        while (loopCol < N_COLS) {
            array1[loopRow][loopCol] = array[loopRow][loopCol];
            loopCol ++;
        }
        loopRow ++;
    }

    int loopStartRow = start_row;
    int targetStartRow = target_row; 
    int targetEndCol = target_col + end_col - start_col;
    int targetEndRow = target_row + end_row - start_row;
    int loopA = 0;
    if (targetStartRow < 0) {
        loopStartRow = loopStartRow + (0 - targetStartRow);
        targetStartRow = 0;
    }

    while (loopA == 0) {
        int loopStartCol = start_col;
        int targetStartCol = target_col;
        if (targetStartCol < 0) {
            loopStartCol = loopStartCol + (0 - targetStartCol);
            targetStartCol = 0;
        }
        int loopB = 0;
        while (loopB == 0) {
            array[targetStartRow][targetStartCol] = array1[loopStartRow][loopStartCol];
            targetStartCol ++;
            loopStartCol ++;
            if (targetStartCol > targetEndCol) {
                loopB = 1;
            }
            if (targetStartCol >= 36) {
                loopB = 1;
            }
        }
        targetStartRow ++;
        loopStartRow ++;
        if (targetStartRow > targetEndRow) {
            loopA = 1;
        }
        if (targetStartRow >= 20) {
            loopA = 1;
        }
    }
}

int check(int arrayA[N_ROWS][N_COLS], int arrayB[N_ROWS][N_COLS]) {
    int a = 0;
    int loopA = 0;
    int loopEquid = 0;
    while (loopA < N_ROWS) {
        int loopB = 0;
        while (loopEquid == 0 && loopB < N_COLS) {
            if (arrayA[loopA][loopB] !=  arrayB[loopA][loopB]) {
                loopEquid = 1;
            }
            loopB ++;
        }
        loopA ++;
    }
    if (loopEquid == 1) {
        a ++;
    }
    return a;
}

void saveArray(int arrayA[N_ROWS][N_COLS], int arrayB[N_ROWS][N_COLS]) {
    int loopA = 0;
    while (loopA < N_ROWS) {
        int loopB = 0;
        while (loopB < N_COLS) {
            arrayA[loopA][loopB] =  arrayB[loopA][loopB];
            loopB ++;
        }
        loopA ++;
    }
}
// ADD CODE FOR YOUR FUNCTIONS HERE



// Displays the canvas, by printing the integer value stored in
// each element of the 2-dimensional canvas array.
//
// You should not need to change the displayCanvas function.
void displayCanvas(int canvas[N_ROWS][N_COLS]) {
    int row = 0;
    while (row < N_ROWS) {
        int col = 0;
        while (col < N_COLS) {
            printf("%d ", canvas[row][col]);
            col++;
        }
        row++;
        printf("\n");
    }
}


// Sets the entire canvas to be blank, by setting each element in the
// 2-dimensional canvas array to be WHITE (which is #defined at the top
// of the file).
//
// You should not need to change the clearCanvas function.
void clearCanvas(int canvas[N_ROWS][N_COLS]) {
    int row = 0;
    while (row < N_ROWS) {
        int col = 0;
        while (col < N_COLS) {
            canvas[row][col] = WHITE;
            col++;
        }
        row++;
    }
}

