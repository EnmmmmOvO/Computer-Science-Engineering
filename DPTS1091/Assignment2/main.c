//
// DO NOT CHANGE THIS FILE
//
// You do not submit this file. This file is not marked.
// If you think you need to change this file you have
// misunderstood the assignment - ask in the course forum.
//
// Assignment 2 DPST1091: CS Pizzeria
// main.c
//
// Version 1.0.0: Release
// Version 1.0.1: Update - Removed `do_free_pizzeria()` prototype (unused)
//
// This file allows you to interactively test the functions you
// implement in pizzeria.c

#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include <string.h>
#include <fcntl.h>
#include <unistd.h>

#include "pizzeria.h"

#define MAX_LINE 2048

// Complete
#define COMMAND_HELP 'h'
#define COMMAND_COMMENT '/'
#define COMMAND_QUIT 'q'

// Stage 1
#define COMMAND_ADD_ORDER 'o'
#define COMMAND_PRINT_PIZZERIA 'p'
#define COMMAND_NEXT_DEADLINE '!'

// Stage 2
#define COMMAND_SELECT_NEXT_ORDER '>'
#define COMMAND_SELECT_PREV_ORDER '<'
#define COMMAND_ADD_INGREDIENT 'i'
#define COMMAND_TOTAL_PROFIT 't'

// Stage 3
#define COMMAND_CANCEL_ORDER 'c'
#define COMMAND_REFILL_STOCK 'r'
#define COMMAND_PRINT_STOCK 's'
#define COMMAND_CAN_COMPLETE_ORDER '?'

// Stage 4
#define COMMAND_COMPLETE_ORDER '#'
#define COMMAND_SAVE_INGREDIENTS 'S'
#define COMMAND_LOAD_INGREDIENTS 'L'

// Command Returns
#define RETURN_EXIT 0
#define RETURN_SILENT 1
#define RETURN_PRINT 2


// Helper Functions
static void do_print_intro(void);
static void *not_null(void *ptr);
static int get_command(char *command, int max_command_length);
static int run_command(struct pizzeria *pizzeria, char *line);

// Do: Completed
static void do_print_help();

// Do: Stage 1
static void do_add_order(struct pizzeria *pizzeria, char *line);
static void do_print_all_orders(struct pizzeria *pizzeria, char *line);
static void do_next_deadline(struct pizzeria *pizzeria, char *line);

// Do: Stage 2
static void do_select_next_order(struct pizzeria *pizzeria, char *line);
static void do_select_previous_order(struct pizzeria *pizzeria, char *line);
static void do_add_ingredient(struct pizzeria *pizzeria, char *line);
static void do_calculate_total_profit(struct pizzeria *pizzeria, char *line);

// Do: Stage 3
static void do_cancel_order(struct pizzeria *pizzeria, char *line);
static void do_refill_stock(struct pizzeria *pizzeria, char *line);
static void do_print_stock(struct pizzeria *pizzeria, char *line);
static void do_can_complete_order(struct pizzeria *pizzeria, char *line);

// Do: Stage 4
static void do_complete_order(struct pizzeria *pizzeria, char *line);
static void do_save_ingredients(struct pizzeria *pizzeria, char *line);
static void do_load_ingredients(struct pizzeria *pizzeria, char *line);

int main(void) {
    do_print_intro();

    char line[MAX_LINE];

    struct pizzeria *pizzeria = create_pizzeria();

    int command_number = 0;
    int read_command = RETURN_PRINT;
    while (read_command) {
        printf("%03d: ", command_number++);
        read_command = get_command(line, MAX_LINE);
        if (read_command) read_command *= run_command(pizzeria, line);
    }

    free_pizzeria(not_null(pizzeria));
    return 0;
}

static void do_print_intro(void) {
    printf("===========================[ CS Pizzeria ]==========================\n");
    printf("Welcome to CS Pizzeria! Type 'h' to see help.\n");
    printf("====================================================================\n");
}

static void *not_null(void *ptr) {
    if (ptr != NULL) {
        return ptr;
    }
    fprintf(stderr, "This solution was going to pass a NULL pointer.\n");
    fprintf(stderr, "You have probably not implemented a required function.\n");
    fprintf(
        stderr,
        "If you believe this message is in error, post on the course forum.\n"
    );
    exit(1);
}

static int get_command(char *command, int max_command_length) {

    if (fgets(command, max_command_length, stdin) == NULL) {
        return 0;
    }

    // remove '\n' if present
    command[strcspn(command, "\n")] = '\0';

    int leading_whitespace = 0;
    while (isspace(command[leading_whitespace])) {
        leading_whitespace++;
    }
    char *old_location = command;
    char *new_location = command + leading_whitespace;
    size_t length = MAX_LINE - leading_whitespace;
    memmove(old_location, new_location, length);

    return 1;
}

static int run_command(struct pizzeria *pizzeria, char *line) {
    if (line[0] == COMMAND_HELP) {
        do_print_help();
        return RETURN_SILENT;
    } else if (line[0] == COMMAND_COMMENT) {
        return RETURN_SILENT;
    } else if (line[0] == COMMAND_QUIT) {
        return RETURN_EXIT;
    } else if (line[0] == COMMAND_ADD_ORDER) {
        do_add_order(pizzeria, line);
        return RETURN_PRINT;
    } else if (line[0] == COMMAND_PRINT_PIZZERIA) {
        do_print_all_orders(pizzeria, line);
        return RETURN_PRINT;
    } else if (line[0] == COMMAND_NEXT_DEADLINE) {
        do_next_deadline(pizzeria, line);
        return RETURN_PRINT;
    } else if (line[0] == COMMAND_SELECT_NEXT_ORDER) {
        do_select_next_order(pizzeria, line);
        return RETURN_PRINT;
    } else if (line[0] == COMMAND_SELECT_PREV_ORDER) {
        do_select_previous_order(pizzeria, line);
        return RETURN_PRINT;
    } else if (line[0] == COMMAND_ADD_INGREDIENT) {
        do_add_ingredient(pizzeria, line);
        return RETURN_PRINT;
    } else if (line[0] == COMMAND_TOTAL_PROFIT) {
        do_calculate_total_profit(pizzeria, line);
        return RETURN_PRINT;
    } else if (line[0] == COMMAND_CANCEL_ORDER) {
        do_cancel_order(pizzeria, line);
        return RETURN_PRINT;
    } else if (line[0] == COMMAND_REFILL_STOCK) {
        do_refill_stock(pizzeria, line);
        return RETURN_PRINT;
    } else if (line[0] == COMMAND_PRINT_STOCK) {
        do_print_stock(pizzeria, line);
        return RETURN_PRINT;
    } else if(line[0] == COMMAND_CAN_COMPLETE_ORDER) {
        do_can_complete_order(pizzeria, line);
        return RETURN_PRINT;
    } else if (line[0] == COMMAND_COMPLETE_ORDER) {
        do_complete_order(pizzeria, line);
        return RETURN_PRINT;
    } else if (line[0] == COMMAND_SAVE_INGREDIENTS) {
        do_save_ingredients(pizzeria, line);
        return RETURN_PRINT;
    } else if (line[0] == COMMAND_LOAD_INGREDIENTS) {
        do_load_ingredients(pizzeria, line);
        return RETURN_PRINT;
    } else if (line[0] == '\0') {
        return RETURN_SILENT;
    } else {
        printf("Invalid command %c, use 'h' to get help!\n", line[0]);
        return RETURN_SILENT;
    }
}


static void do_print_help() {
    printf(""
        "============================[ Help ]============================\n"
    );

    printf(""
        "  %c\n"
        "    Show this help screen.\n",
        COMMAND_HELP
    );
    printf(""
        "  %c\n"
        "    Quit this program.\n",
        COMMAND_QUIT
    );
    printf("\n---------------------------[ Stage 1 ]---------------------------\n");
    printf(""
        "  %c <customer_name> <pizza_name> <price (xx.xx)> <time_allowed>\n"
        "    Add an order to the Pizzeria.\n",
        COMMAND_ADD_ORDER
    );
    printf(""
        "  %c\n"
        "    Print all orders in the Pizzeria.\n",
        COMMAND_PRINT_PIZZERIA
    );
    printf(""
        "  %c\n"
        "    Gets the shortest waiting time of all orders in the Pizzeria\n",
        COMMAND_NEXT_DEADLINE
    );
    printf("\n---------------------------[ Stage 2 ]---------------------------\n");
    printf(""
        "  %c\n"
        "    Move the currently selected order to the next order. \n"
        "    If at last order before command used, no order will be selected"
        "    after use.\n"
        "    If no order selected before command used, first order will be"
        "    selected after use.\n",
        COMMAND_SELECT_NEXT_ORDER
    );
    printf(""
        "  %c\n"
        "    Move the currently selected order to the previous order. \n"
        "    If at first order before command used, no order will be selected"
        "    after use.\n"
        "    If no order selected before command used, last order will be"
        "    selected after use.\n",
        COMMAND_SELECT_PREV_ORDER
    );
    printf(""
        "  %c <ingredient_name> <amount> <price (xx.xx)>\n"
        "    Adds an ingredient to the currently selected order.\n",
        COMMAND_ADD_INGREDIENT
    );
    printf(""
        "  %c\n"
        "    Gets the total profit to be made from the currently selected"
        "    order.\n",
        COMMAND_TOTAL_PROFIT
    );
    printf("\n---------------------------[ Stage 3 ]---------------------------\n");
    printf(""
        "  %c\n"
        "    Cancel the current order, if there is one.\n",
        COMMAND_CANCEL_ORDER
    );
    printf(""
        "  %c <ingredient_name> <amount> <price (xx.xx)>\n"
        "    Refills the stock with given ingredient\n",
        COMMAND_REFILL_STOCK
    );
    printf(""
        " %c\n"
        "   Prints out the ingredients in the stock\n",
        COMMAND_PRINT_STOCK
    );
    printf(""
        "  %c\n"
        "    Determines if the currently selected order can be completed\n",
        COMMAND_CAN_COMPLETE_ORDER
    );
}

////////////////////////////////////////////////////////////////////////
//                         Stage 1 Functions                          //
////////////////////////////////////////////////////////////////////////

static void do_add_order(struct pizzeria *pizzeria, char *line) {
    char customer[MAX_LINE];
    char pizza_name[MAX_LINE];
    double price;
    int time_allowed;
    char command;

    int scanf_return = sscanf(
        line, "%c %s %s %lf %d", &command, customer, pizza_name,
        &price, &time_allowed
    );

    if (scanf_return != 5) {
        printf(""
            "Command Invalid. The correct format is: %c <customer_name> "
            "<pizza_name> <price (xx.xx)> <time_allowed>.\n",
            command
        );
        return;
    }

    int add_order_result = add_order(
        not_null(pizzeria), customer, pizza_name, price, time_allowed
    );

    if (add_order_result == INVALID_PRICE) {
        printf("Invalid price - price '%.2lf' must be non-negative.\n", price);
    } else if (add_order_result == INVALID_TIME) {
        printf("Invalid time - time allowed '%d' must be positive.\n", time_allowed);
    } else if (add_order_result == SUCCESS) {
        printf("Added order successfully!\n");
    } else {
        printf("ERROR: Unknown return value!\n");
    }
}

static void do_print_all_orders(struct pizzeria *pizzeria, char *line) {
    // we pass line for consistency, but don't need it.
    (void) line;

    print_all_orders(not_null(pizzeria));
}

static void do_next_deadline(struct pizzeria *pizzeria, char *line) {
    int deadline_result = next_deadline(not_null(pizzeria));

    if (deadline_result == INVALID_CALL) {
        printf("There are currently no orders in the Pizzeria.\n");
    } else {
        printf(""
            "The next deadline is in %d minutes\n",
            deadline_result
        );
    }
}

////////////////////////////////////////////////////////////////////////
//                         Stage 2 Functions                          //
////////////////////////////////////////////////////////////////////////

static void do_select_next_order(struct pizzeria *pizzeria, char *line) {
    // we pass line for consistency, but don't need it.
    (void) line;

    select_next_order(pizzeria);
}

static void do_select_previous_order(struct pizzeria *pizzeria, char *line) {
    // we pass line for consistency, but don't need it.
    (void) line;

    select_previous_order(pizzeria);
}

static void do_add_ingredient(struct pizzeria *pizzeria, char *line) {
    char command;
    char ingredient_name[MAX_LINE];
    int amount;
    double price;

    int scanf_return = sscanf(
        line, "%c %s %d %lf", &command, ingredient_name, &amount, &price
    );

    if (scanf_return != 4) {
        printf(""
            "Command Invalid. The correct format is: %c <ingredient_name> "
            "<amount> <price (xx.xx)>.\n",
            command
        );
        return;
    }
    int add_ingredient_result = add_ingredient(
        not_null(pizzeria), ingredient_name, amount, price
    );

    if (add_ingredient_result == INVALID_ORDER) {
        printf("There is no currently selected order.\n");
    } else if (add_ingredient_result == INVALID_PRICE) {
        printf("The price %.2lf must be non-negative.\n", price);
    } else if (add_ingredient_result == INVALID_AMOUNT) {
        printf("There amount %d must be positive.\n", amount);
    } else if (add_ingredient_result == SUCCESS) {
        printf("Ingredient added successfully!\n");
    } else {
        printf("ERROR: Unknown return value!\n");
    }
}

static void do_calculate_total_profit(struct pizzeria *pizzeria, char *line) {
    // we pass line for consistency, but don't need it.
    (void) line;

    double profit_result = calculate_total_profit(not_null(pizzeria));

    if (profit_result == INVALID_ORDER) {
        printf("There is no currently selected order.\n");
    } else {
        printf("The total profit from this order is $%.2lf\n", profit_result);
    }
}


////////////////////////////////////////////////////////////////////////
//                         Stage 3 Functions                          //
////////////////////////////////////////////////////////////////////////

static void do_cancel_order(struct pizzeria *pizzeria, char *line) {
    // we pass line for consistency, but don't need it.
    (void) line;

    int cancel_order_result = cancel_order(not_null(pizzeria));

    if (cancel_order_result == INVALID_ORDER) {
        printf("There is no order currently selected!\n");
    } else {
        printf("Selected order has been cancelled!\n");
    }
}

static void do_refill_stock(struct pizzeria *pizzeria, char *line) {
    char command;
    char ingredient_name[MAX_LINE];
    int amount;
    double price;

    int scanf_return = sscanf(
        line, "%c %s %d %lf", &command, ingredient_name, &amount, &price
    );

    if (scanf_return != 4) {
        printf(""
            "Command Invalid. The correct format is: %c <ingredient_name> "
            "<amount> <price (xx.xx)>.\n",
            command
        );
        return;
    }
    int refill_stock_result = refill_stock(
        not_null(pizzeria), ingredient_name, amount, price
    );

    if (refill_stock_result == INVALID_PRICE) {
        printf("The price %.2lf must be non-negative.\n", price);
    } else if (refill_stock_result == INVALID_AMOUNT) {
        printf("There amount %d must be positive.\n", amount);
    } else if (refill_stock_result == SUCCESS) {
        printf("Ingredient added successfully!\n");
    } else {
        printf("ERROR: Unknown return value!\n");
    }
}

static void do_print_stock(struct pizzeria *pizzeria, char *line) {
    // we pass line for consistency, but don't need it.
    (void) line;

    print_stock(not_null(pizzeria));
}

static void do_can_complete_order(struct pizzeria *pizzeria, char *line) {
    // we pass line for consistency, but don't need it.
    (void) line;

    int can_complete_result = can_complete_order(not_null(pizzeria));

    if (can_complete_result == INVALID_ORDER) {
        printf("There is no order currently selected, or the selected order has "
               "no ingredients in it!\n");
    } else if (can_complete_result == INSUFFICIENT_STOCK) {
        printf("There are not enough items in the stock for this order to be "
               "completed!\n"
        );
    } else if (can_complete_result == SUCCESS) {
        printf("The selected order can be completed!\n");
    } else {
        printf("ERROR: Unknown return value!\n");
    }
}

static void do_complete_order(struct pizzeria *pizzeria, char *line) {
    // we pass line for consistency, but don't need it.
    (void) line;

    int complete_result = complete_order(not_null(pizzeria));

    if (complete_result == INVALID_ORDER) {
        printf("There is no order currently selected, or the selected order has "
               "no ingredients in it!\n");
    } else if (complete_result == INSUFFICIENT_STOCK) {
        printf("There are not enough items in the stock for this order to be "
               "completed!\n"
        );
    } else if (complete_result == SUCCESS) {
        printf("The selected order has been completed!\n");
    } else {
        printf("ERROR: Unknown return value!\n");
    }
}

static void do_save_ingredients(struct pizzeria *pizzeria, char *line) {
    char command;
    char file_name[MAX_LINE];
    int scanf_return = sscanf(
        line, "%c %s", &command, file_name
    );

    if (scanf_return != 2) {
        printf(""
            "Command Invalid. The correct format is: %c <file_name> ",
            command
        );
        return;
    }

    int save_result = save_ingredients(not_null(pizzeria), file_name);
    if (save_result == INVALID_ORDER) {
        printf("There is no order currently selected!\n");
    } else if (save_result == SUCCESS) {
        printf("Order has successfully been saved into file '%s.txt'\n", file_name);
    } else {
        printf("ERROR: Unknown return value!\n");
    }
}

static void do_load_ingredients(struct pizzeria *pizzeria, char *line) {
    char command;
    char file_name[MAX_LINE];
    int scanf_return = sscanf(
        line, "%c %s", &command, file_name
    );

    if (scanf_return != 2) {
        printf(""
            "Command Invalid. The correct format is: %c <file_name> ",
            command
        );
        return;
    }

    int load_result = load_ingredients(not_null(pizzeria), file_name);
    if (load_result == INVALID_ORDER) {
        printf("There is no order currently selected!\n");
    } else if (load_result == SUCCESS) {
        printf("Order has successfully been loaded from file '%s.txt'\n", file_name);
    } else {
        printf("ERROR: Unknown return value!\n");
    }
}
