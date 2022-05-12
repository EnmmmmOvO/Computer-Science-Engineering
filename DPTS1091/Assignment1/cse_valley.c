// CSE Valley
// cse_valley.c
//
// This program was written by Leonard Xu(Xiaoyi Xu) (z5286061)
// on 04-03-2022
//
// Version 1.0.0 (2021-10-04): Assignment Released.
//
// TODO: Description of your progranew_matrix.

#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>

#define MAX_NAME_SIZE 50
#define MAX_NUM_SEED_TYPES 26
#define LAND_SIZE 8
#define NO_SEED ' '
#define TRUE 1
#define FALSE 0

struct land {
    int is_watered;
    char seed_name;
};

struct seeds {
    char name;
    int amount;
};

struct farmer {
    int curr_col;
    int curr_row;
    char curr_dir;
};

struct matrix { 
    int col;
    int row;
};



// HINT: You will be using this function in stage 2!
void print_land(struct land farm_land[LAND_SIZE][LAND_SIZE], struct farmer cse_farmer);
void search_name(struct seeds seed_collection[MAX_NUM_SEED_TYPES], 
                 char seed_name, int seed_number);
int check_direction(char command);
struct matrix check_front(struct land farm_land[LAND_SIZE][LAND_SIZE], 
                          struct farmer cse_farmer);
void check_water(struct land farm_land[LAND_SIZE][LAND_SIZE], struct farmer cse_farmer);
void check_plant(struct land farm_land[LAND_SIZE][LAND_SIZE], struct farmer cse_farmer, 
                 struct seeds seed_collection[MAX_NUM_SEED_TYPES], char seed, 
                 int seed_number);
void check_line_plant(struct land farm_land[LAND_SIZE][LAND_SIZE], 
                      struct farmer cse_farmer, 
                      struct seeds seed_collection[MAX_NUM_SEED_TYPES], 
                      char plant_line_seed, int seed_number);
void water_square(struct land farm_land[LAND_SIZE][LAND_SIZE], struct farmer cse_farmer,
                  int size);
void next_day(struct land farm_land[LAND_SIZE][LAND_SIZE]);
void harvest_adjacant_land(struct land farm_land[LAND_SIZE][LAND_SIZE], 
                           struct seeds seed_collection[MAX_NUM_SEED_TYPES], 
                           struct farmer cse_farmer,
                           int seed_number);


// Provided functions use for game setup
// You do not need to use these functions yourself.
struct farmer initialise_farmer(struct farmer cse_farmer);
void initialise_seeds(struct seeds seed_collection[MAX_NUM_SEED_TYPES]);
void initialise_land(struct land farm_land[LAND_SIZE][LAND_SIZE]);
void print_top_row(struct land farm_land[LAND_SIZE][LAND_SIZE], int row);
void print_farmer_row(struct land farm_land[LAND_SIZE][LAND_SIZE], 
                      struct farmer cse_farmer);

int main(void) {

    struct farmer cse_farmer = {};
    cse_farmer = initialise_farmer(cse_farmer);

    struct land farm_land[LAND_SIZE][LAND_SIZE];
    initialise_land(farm_land);

    struct seeds seed_collection[MAX_NUM_SEED_TYPES];
    initialise_seeds(seed_collection);

    printf("Welcome to CSE Valley, farmer!\n");
    printf("Congratulations, you have received 60 seeds.\n");
    printf("How many different seeds do you wish to have? ");
    
    int seed_number = 0;
    scanf("%d", &seed_number);

    printf("Enter the names of the seeds to be given:\n");
    
    for (int loop = 0; loop < seed_number; loop++) {
        getchar();
        scanf("%c", &seed_collection[loop].name);
        seed_collection[loop].amount = 60/seed_number;
    }

    printf("Game Started!\n");
    
    int day = 1;
    char command;
    printf("Enter command: ");
    getchar();
    while (scanf("%c", &command) != -1) {  
        if (command == '\n') continue;  
        if (command == 'a') {
            printf("  Seeds at your disposal:\n");
            for (int loop = 0; loop < seed_number; loop++) 
                printf("  - %d seed(s) with the name '%c'\n", 
                seed_collection[loop].amount, seed_collection[loop].name);
        } else if (command == 's') {
            char seed_name;
            getchar();
            scanf("%c", &seed_name);
            if (seed_name < 'a' || seed_name > 'z') {
                printf("  Seed name has to be a lowercase letter\n");
                printf("Enter command: ");
                getchar();
                continue;
            }
            search_name(seed_collection, seed_name, seed_number);
            
        } else if (command == 'l') {
            print_land(farm_land, cse_farmer);
        } else if (check_direction(command)) {
            if (cse_farmer.curr_dir != command) {
                cse_farmer.curr_dir = command;
            } else {
                if (command == '>' && cse_farmer.curr_col < LAND_SIZE - 1) 
                    cse_farmer.curr_col++;
                if (command == '<' && cse_farmer.curr_col > 0) 
                    cse_farmer.curr_col--;
                if (command == '^' && cse_farmer.curr_row > 0) 
                    cse_farmer.curr_row--;
                if (command == 'v' && cse_farmer.curr_row < LAND_SIZE - 1) 
                    cse_farmer.curr_row++;
            }      
        } else if (command == 'o') {
            char water_or_plant;
            getchar();
            scanf("%c", &water_or_plant);
            
            if (water_or_plant == 'w') {
                check_water(farm_land, cse_farmer);
            } else if (water_or_plant == 'p') {
                char plant_seed_name;
                getchar();
                scanf("%c", &plant_seed_name);
                check_plant(farm_land, cse_farmer, seed_collection, 
                            plant_seed_name, seed_number);
            }
        } else if (command == 'p') {
            char plant_line_seed;
            getchar();
            scanf("%c", &plant_line_seed);
            check_line_plant(farm_land, cse_farmer, seed_collection, 
                             plant_line_seed, seed_number);
        } else if (command == 'w') {
            getchar();
            int size;
            scanf("%d", &size);
            if (size < 0) {
                printf("  The size argument needs to be a non-negative integer\n");
            } else {
                water_square(farm_land, cse_farmer, size);
            }
        } else if (command == 'n') {
            day++;
            printf("  Advancing to the next day... Day %d, let's go!\n", day);
            cse_farmer = initialise_farmer(cse_farmer);
            next_day(farm_land);
        } else if (command == 'h') {
            harvest_adjacant_land(farm_land, seed_collection, cse_farmer, seed_number);
        } else if (command == 't') {
            getchar();
            char trade_use;
            scanf("%c", &trade_use);
            
            getchar();
            int size;
            scanf("%d", &size);

            getchar();
            char trade_purpose;
            scanf("%c", &trade_purpose);

            if (!islower(trade_use)) {
                printf("  Seed name has to be a lowercase letter\n");
                printf("Enter command: ");
                getchar();
                continue;
            }

            if (size < 0) {
                printf("  You can't trade negative seeds\n");
                printf("Enter command: ");
                getchar();
                continue;
            }

            int position_use = -1;
            int position_purpose = -1;
            for (int loop = 0; loop < seed_number; loop++) {
                if (seed_collection[loop].name == trade_use)
                    position_use = loop;
                if (seed_collection[loop].name == trade_purpose)
                    position_purpose = loop;
            }

            if (position_use == -1) {
                printf("  You don't have the seeds to be traded\n");
                printf("Enter command: ");
                getchar();
                continue;
            }

            if (seed_collection[position_use].amount < size) {
                printf("  You don't have enough seeds to be traded\n");
                printf("Enter command: ");
                getchar();
                continue;
            }
            
            if (!islower(trade_purpose)) {
                printf("   Seed name has to be a lowercase letter\n");
                printf("Enter command: ");
                getchar();
                continue;
            }
            

            seed_collection[position_use].amount -= size;

            if (position_purpose != -1) {
                seed_collection[position_purpose].amount += size;
            } else {
                for (int loop = seed_number; loop > 0; loop--)
                    seed_collection[loop] = seed_collection[loop - 1];
                seed_collection[0].amount = size;
                seed_collection[0].name = trade_purpose;
                seed_number++;
            }

        }
        printf("Enter command: ");
        getchar();
    }

    return 0;
}


void search_name(struct seeds seed_collection[MAX_NUM_SEED_TYPES], 
                 char seed_name, int seed_number) {
    int check = 0;
    for (int loop = 0; loop < seed_number; loop++) {
        if (seed_name == seed_collection[loop].name) {
            printf("  There are %d seeds with the name '%c'\n",
                    seed_collection[loop].amount, seed_name);
            check = 1;
            break;
        }
    }
    if (check == 0) 
        printf("  There is no seed with the name '%c'\n", seed_name);
}

int check_direction(char command) {
    if (command == '>' || command == 'v' 
        || command == '<' || command == '^') return 1;
    return 0;
}


struct matrix check_front(struct land farm_land[LAND_SIZE][LAND_SIZE], 
                          struct farmer cse_farmer) {

    struct matrix new_matrix;
    new_matrix.col = cse_farmer.curr_col;
    new_matrix.row = cse_farmer.curr_row;

    switch (cse_farmer.curr_dir) {
        case '>': new_matrix.col++; break;
        case '<': new_matrix.col--; break;
        case '^': new_matrix.row--; break;
        case 'v': new_matrix.row++; break;
        default: break;
    }

    return new_matrix;
}

void check_water(struct land farm_land[LAND_SIZE][LAND_SIZE], struct farmer cse_farmer) {
    struct matrix new_matrix = check_front(farm_land, cse_farmer);

    if (new_matrix.col >= 0 && new_matrix.row <= LAND_SIZE 
        && new_matrix.col <= LAND_SIZE && new_matrix.row >= 0)
        farm_land[new_matrix.row][new_matrix.col].is_watered = 1;
}

void check_plant(struct land farm_land[LAND_SIZE][LAND_SIZE], struct farmer cse_farmer, 
                 struct seeds seed_collection[MAX_NUM_SEED_TYPES], char seed, 
                 int seed_number) {
    struct matrix new_matrix = check_front(farm_land, cse_farmer);

    if (!(new_matrix.col >= 0 && new_matrix.row <= LAND_SIZE 
        && new_matrix.col <= LAND_SIZE && new_matrix.row >= 0)) return;
    farm_land[new_matrix.row][new_matrix.col].seed_name = seed; 
    
    for (int loop = 0; loop < seed_number; loop++) { 
        if (seed_collection[loop].name == seed) seed_collection[loop].amount--;
    }   
}

void check_line_plant(struct land farm_land[LAND_SIZE][LAND_SIZE], 
                      struct farmer cse_farmer, 
                      struct seeds seed_collection[MAX_NUM_SEED_TYPES], 
                      char plant_line_seed, int seed_number) {

    if (!(plant_line_seed >= 'a' && plant_line_seed <= 'z')) {
        printf("  Seed name has to be a lowercase letter\n");
        return;
    }   

    int position = -1;
    for (int loop = 0; loop < seed_number; loop++) {
        if (seed_collection[loop].name == plant_line_seed) {
            position = loop;
            break;
        }
    }

    if (position == -1) {
        printf("  There is no seed with the name '%c'\n", plant_line_seed);
        return;
    }

    if (cse_farmer.curr_dir == '^' || cse_farmer.curr_dir == '<') {
        printf("  You cannot scatter seeds ^ or <\n");
        return;
    }

    if (cse_farmer.curr_dir == '>') {
        for (int loop = cse_farmer.curr_col; loop < LAND_SIZE; loop++) {
            if (seed_collection[position].amount > 0) {
                seed_collection[position].amount--;
                farm_land[cse_farmer.curr_row][loop].seed_name = plant_line_seed;
            }
        }
    } else if (cse_farmer.curr_dir == 'v') {
        for (int loop = cse_farmer.curr_row; loop < LAND_SIZE; loop++) {
            if (seed_collection[position].amount > 0) {
                seed_collection[position].amount--;
                farm_land[loop][cse_farmer.curr_col].seed_name = plant_line_seed;
            }
        }
    }
}

void water_square(struct land farm_land[LAND_SIZE][LAND_SIZE], struct farmer cse_farmer,
                  int size) {
    struct matrix start;
    struct matrix end;
    start.col = cse_farmer.curr_col - size < 0 ? 0 : cse_farmer.curr_col - size;
    start.row = cse_farmer.curr_row - size < 0 ? 0 : cse_farmer.curr_row - size;
    end.col = cse_farmer.curr_col + size < LAND_SIZE ? 
              cse_farmer.curr_col + size : LAND_SIZE - 1;
    end.row = cse_farmer.curr_row + size < LAND_SIZE ? 
              cse_farmer.curr_row + size : LAND_SIZE - 1;

    for (int loop_col = start.col; loop_col <= end.col; loop_col++) {
        for (int loop_row = start.row; loop_row <= end.row; loop_row++)
            farm_land[loop_row][loop_col].is_watered = 1;
    }

}

void next_day(struct land farm_land[LAND_SIZE][LAND_SIZE]) {
    for (int loop_col = 0; loop_col < LAND_SIZE; loop_col++) {
        for (int loop_row = 0; loop_row < LAND_SIZE; loop_row++) {
            if (farm_land[loop_row][loop_col].is_watered == 0) {
                farm_land[loop_row][loop_col].seed_name = NO_SEED;
            } else if (farm_land[loop_row][loop_col].is_watered == 1 && 
                       islower(farm_land[loop_row][loop_col].seed_name)) {
                farm_land[loop_row][loop_col].is_watered = 0;
                farm_land[loop_row][loop_col].seed_name = 
                    toupper(farm_land[loop_row][loop_col].seed_name);
            } else if (isupper(farm_land[loop_row][loop_col].seed_name)) {
                farm_land[loop_row][loop_col].seed_name = NO_SEED;
            }
        }
    }  
}

void harvest_adjacant_land(struct land farm_land[LAND_SIZE][LAND_SIZE], 
                           struct seeds seed_collection[MAX_NUM_SEED_TYPES], 
                           struct farmer cse_farmer,
                           int seed_number) {
    struct matrix purpose;
    purpose.col = cse_farmer.curr_col;
    purpose.row = cse_farmer.curr_row;

    switch (cse_farmer.curr_dir) {
        case '>': purpose.col++; break;
        case 'v': purpose.row++; break;
        case '<': purpose.col--; break;
        case '^': purpose.row--; break;
        default: break;
    }

    if (purpose.col >= 0 && purpose.col <= LAND_SIZE &&
        purpose.row >= 0 && purpose.row <= LAND_SIZE && 
        isupper(farm_land[purpose.row][purpose.col].seed_name)) {

        printf("  Plant '%c' was harvested, resulting in %d '%c' seed(s)\n",
               farm_land[purpose.row][purpose.col].seed_name, 5, 
               tolower(farm_land[purpose.row][purpose.col].seed_name));
        

        for (int loop = 0; loop < seed_number; loop++) {
            if (seed_collection[loop].name == 
                tolower(farm_land[purpose.row][purpose.col].seed_name)) {
                seed_collection[loop].amount += 5;
            }
        }
        farm_land[purpose.row][purpose.col].seed_name = NO_SEED;
    }
    
}



////////////////////////////////
//     Provided Functions     //
////////////////////////////////

// Prints the structs land (including locating where the
// farmer is)
// You will need this function in Stage 2.
void print_land(struct land farm_land[LAND_SIZE][LAND_SIZE],
                struct farmer cse_farmer) {
    printf("|---|---|---|---|---|---|---|---|\n");
    int i = 0;
    while (i < LAND_SIZE) {
        print_top_row(farm_land, i);
        // only prints mid and bottom row when the farmer
        // is in that row
        if (i == cse_farmer.curr_row) {
            print_farmer_row(farm_land, cse_farmer);
        }
        printf("|---|---|---|---|---|---|---|---|\n");
        i++;
    }
}

// NOTE: You do not need to directly call any of the functions
// below this point. You are allowed to modify them, but you
// do not need to.

// Initialises struct farmer to its default state upon starting
// in which the farmer will be on the top left of the farm
// facing to the right (as noted by '>')
struct farmer initialise_farmer(struct farmer cse_farmer) {
    cse_farmer.curr_col = 0;
    cse_farmer.curr_row = 0;
    cse_farmer.curr_dir = '>';
    return cse_farmer;
}

// Initialises a 2d array of struct land to its default state 
// upon starting, which is that all land is unwatered and
// contains no seed
void initialise_land(struct land farm_land[LAND_SIZE][LAND_SIZE]) {
    int i = 0;
    while (i < LAND_SIZE) {
        int j = 0;
        while (j < LAND_SIZE) {
            farm_land[i][j].is_watered = FALSE;
            farm_land[i][j].seed_name = NO_SEED;
            j++;
        }
        i++;
    }
}

// Initialises struct farmer to its default state upon starting,
// which that all names are initialised as NO_SEED and its
// amount is 0
void initialise_seeds(struct seeds seed_collection[MAX_NUM_SEED_TYPES]) {
    int i = 0;
    while (i < MAX_NUM_SEED_TYPES) {
        seed_collection[i].amount = 0;
        seed_collection[i].name = NO_SEED;
        i++;
    }
}

////////////////////////////////
//      Helper Functions      //
////////////////////////////////

// prints the top row of a particular struct land
void print_top_row(struct land farm_land[LAND_SIZE][LAND_SIZE], int row) {
    int j = 0;
    while (j < LAND_SIZE) {
        printf("|");
        printf("%c", farm_land[row][j].seed_name);
        printf(" ");
        if (farm_land[row][j].is_watered == TRUE) {
            printf("W");
        } else {
            printf(" ");
        }
        j++;
    }
    printf("|");
    printf("\n");
}

// prints the 2 additional row when a farmer is in
// a particular row
void print_farmer_row(struct land farm_land[LAND_SIZE][LAND_SIZE], 
                      struct farmer cse_farmer)  {
    int j = 0;
    while (j < LAND_SIZE) {
        printf("|");
        if (j == cse_farmer.curr_col) {
            if (cse_farmer.curr_dir == '<') {
                printf("<");
            } else {
                printf(" ");
            }
            if (cse_farmer.curr_dir == '^') {
                printf("^");
            } else {
                printf("f");
            }
            if (cse_farmer.curr_dir == '>') {
                printf(">");
            } else {
                printf(" ");
            }
        } else {
            printf("   ");
        }
        j++;
    }
    printf("|");
    printf("\n");
    j = 0;
    while (j < LAND_SIZE) {
        printf("|");
        if (j == cse_farmer.curr_col) {
            printf(" ");
            if (cse_farmer.curr_dir == 'v') {
                printf("v");
            } else if (cse_farmer.curr_dir == '^') {
                printf("f");
            } else {
                printf(" ");
            }
            printf(" ");
        } else {
            printf("   ");
        }
        j++;
    }
    printf("|");
    printf("\n");
}