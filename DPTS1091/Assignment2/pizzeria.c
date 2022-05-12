//
// Assignment 2 DPST1091: CS Pizzeria
// pizzeria.c
//
// This program was written by XIAOYI XU (z5286061)
// on 22-03-2022
//
// This code mainly uses loops to complete the functions of creating,
// updating, reading, and deleting linked lists. I defined each string
// in the linked list to include a maximum size of 99, and defined a maximum
// of 8096 characters for writing and reading. In the end, I set up two
// functions myself in order to save repeated assign content and to have better
// viewing.
//
// Version 1.0.0: Release

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "pizzeria.h"
#include "save_string.h"

#define MAX_SIZE 99
#define MAX_CHARACTER 8096
#define MAX_INGREDIENT 16

struct ingredient {
    struct ingredient *next;
    char name[MAX_SIZE];
    int amount;
    double price;
};

struct order {
    struct order *next;
    struct order *last;
    char customer[MAX_SIZE];
    char pizza[MAX_SIZE];
    double price;
    int time;
    struct ingredient *ingredient;
};

struct pizzeria {
    struct ingredient *stock;
    struct order *orders;
    struct order *selected;
    int order_number;
};

//////////////////////////////////////////////////////////////////////

// copy the string content
void copy_char(char paste[MAX_SIZE], char *copy);

// delete the node of stock structure
void delete_stock(struct pizzeria *pizzeria, struct ingredient *temp_stock);

// Prints a single order
void print_order(
    int num,
    char *customer,
    char *pizza_name,
    double price,
    int time_allowed
);

// Prints an ingredient given the name, amount and price in the required format.
// This will be needed for stage 2.
void print_ingredient(char *name, int amount, double price);

////////////////////////////////////////////////////////////////////////
//                         Stage 1 Functions                          //
////////////////////////////////////////////////////////////////////////


struct pizzeria *create_pizzeria() {
    // Allocates memory to store a `struct pizzeria` and returns a pointer to
    // it. The variable `new` holds this pointer!
    struct pizzeria *new = malloc(sizeof(struct pizzeria));

    new->order_number = 0;
    new->selected = NULL;
    new->stock = NULL;
    new->orders = NULL;

    // TODO: this function has already been implemented for the current
    // struct pizzeria. When you decide to change struct pizzeria, change
    // this function as well.

    return new;
}

int add_order(
    struct pizzeria *pizzeria,
    char *customer,
    char *pizza_name,
    double price,
    int time_allowed
) {

    if (price < 0) return INVALID_PRICE;
    if (time_allowed <= 0) return INVALID_TIME;

    struct order *new_order = malloc(sizeof(struct order));
    if (new_order == NULL) {
        fprintf(stderr, "error: out of memory\n");
        exit(EXIT_FAILURE);
    }

    //set the structure's information
    copy_char(new_order->customer, customer);
    copy_char(new_order->pizza, pizza_name);
    new_order->price = price;
    new_order->time = time_allowed;
    new_order->next = NULL;
    new_order->last = NULL;
    new_order->ingredient = NULL;

    pizzeria->order_number++;

    // record the next address and last address
    if (pizzeria->orders == NULL) {
        pizzeria->orders = new_order;
    } else {
        struct order *temp_node = pizzeria->orders;
        for (; temp_node->next != NULL; temp_node = temp_node->next);
        temp_node->next = new_order;
        new_order->last = temp_node;
    }

    return SUCCESS;
}

void print_all_orders(struct pizzeria *pizzeria) {

    struct order *print_temp = pizzeria->orders;
    for (int loop = 0; loop < pizzeria->order_number; loop++, 
         print_temp = print_temp->next)
        print_order(loop + 1, print_temp->customer, print_temp->pizza,
                    print_temp->price, print_temp->time);

    print_selected_order(pizzeria);

}

int next_deadline(struct pizzeria *pizzeria) {

    if (pizzeria->order_number == 0) return -1;

    // Record the first order time, and compare with other order allowed time
    // and find the minimum time
    int deadline = pizzeria->orders->time;
    struct order *temp_pizzeria = pizzeria->orders;
    for (; temp_pizzeria != NULL; temp_pizzeria = temp_pizzeria->next)
        deadline = deadline > temp_pizzeria->time ? temp_pizzeria->time : deadline;

    return deadline;
}

////////////////////////////////////////////////////////////////////////
//                         Stage 2 Functions                          //
////////////////////////////////////////////////////////////////////////


void select_next_order(struct pizzeria *pizzeria) {

    if (pizzeria->order_number == 0) return;

    // if the selected is not point an order, set it point the first order
    if (pizzeria->selected == NULL) {
        pizzeria->selected = pizzeria->orders;
        return;
    }

    pizzeria->selected = pizzeria->selected->next;

}

void select_previous_order(struct pizzeria *pizzeria) {

    if (pizzeria->order_number == 0) return;

    // if the selected is not point an order, set it point the last order
    if (pizzeria->selected == NULL) {
        struct order *temp_order = pizzeria->orders;
        for (; temp_order->next != NULL; temp_order = temp_order->next);
        pizzeria->selected = temp_order;
        return;
    }

    pizzeria->selected = pizzeria->selected->last;

}

void print_selected_order(struct pizzeria *pizzeria) {

    if (pizzeria->selected == NULL) {
        printf("\nNo selected order.\n");
    } else {
        printf("\nThe selected order is %s's %s pizza ($%.2lf) due in %d minutes.\n",
               pizzeria->selected->customer, pizzeria->selected->pizza,
               pizzeria->selected->price, pizzeria->selected->time);
        if (pizzeria->selected->ingredient != NULL) {
            struct ingredient *temp_ingredient = pizzeria->selected->ingredient;
            for (; temp_ingredient != NULL; temp_ingredient = temp_ingredient->next)
                print_ingredient(temp_ingredient->name,temp_ingredient->amount,
                                 temp_ingredient->price);
        }
    }
}

int add_ingredient(
    struct pizzeria *pizzeria,
    char *ingredient_name,
    int amount,
    double price
) {

    if (pizzeria->selected == NULL) return INVALID_ORDER;
    if (price < 0) return INVALID_PRICE;
    if (amount < 0) return INVALID_AMOUNT;

    struct ingredient *new_ingredient = malloc(sizeof(struct ingredient));
    if (new_ingredient == NULL) {
        fprintf(stderr, "error: out of memory\n");
        exit(EXIT_FAILURE);
    }

    // set the structure's information
    copy_char(new_ingredient->name,ingredient_name);
    new_ingredient->amount = amount;
    new_ingredient->price = price;
    new_ingredient->next = NULL;

    // exist four situation
    // ingredient is empty
    // ingredient name is in the middle of the ingredient
    // ingredient name is the first position
    // ingredient name is the last position
    if (pizzeria->selected->ingredient == NULL) {
        pizzeria->selected->ingredient = new_ingredient;
    } else {
        struct ingredient *temp_ingredient = pizzeria->selected->ingredient;
        for (; temp_ingredient != NULL; temp_ingredient = temp_ingredient->next) {
            if (strcmp(ingredient_name, temp_ingredient->name) < 0) {
                new_ingredient->next = pizzeria->selected->ingredient;
                pizzeria->selected->ingredient = new_ingredient;
                break;
            }
            if (strcmp(ingredient_name, temp_ingredient->name) > 0 &&
                temp_ingredient->next == NULL) {
                temp_ingredient->next = new_ingredient;
                break;
            }
            if (strcmp(ingredient_name, temp_ingredient->name) > 0 &&
                strcmp(ingredient_name, temp_ingredient->next->name) < 0) {
                new_ingredient->next = temp_ingredient->next;
                temp_ingredient->next = new_ingredient;
                break;
            }
            if (strcmp(ingredient_name, temp_ingredient->name) == 0) {
                temp_ingredient->amount += amount;
                free(new_ingredient);
                break;
            }
        }
    }

    return SUCCESS;
}

double calculate_total_profit(struct pizzeria *pizzeria) {

    if (pizzeria->selected == NULL) return INVALID_ORDER;

    // if the ingredient is empty return price
    double price = pizzeria->selected->price;
    if (pizzeria->selected->ingredient == NULL) return price;

    // total = price - (ingredient amount * price)
    struct ingredient *temp_ingredient = pizzeria->selected->ingredient;
    for (; temp_ingredient != NULL; temp_ingredient = temp_ingredient->next)
        price -= temp_ingredient->price * temp_ingredient->amount;
    return price;

}

////////////////////////////////////////////////////////////////////////
//                         Stage 3 Functions                          //
////////////////////////////////////////////////////////////////////////


int cancel_order(struct pizzeria *pizzeria) {

    if (pizzeria->selected == NULL) return INVALID_ORDER;

    // exist three situation
    // a. cancel the first order
    // b. cancel the middle order
    // c, cancle the last order
    struct order *cancel_order = pizzeria->selected;
    if (cancel_order->next == NULL && cancel_order->last == NULL) {
        pizzeria->orders = NULL;
        pizzeria->selected = NULL;
    } else if (cancel_order->next == NULL) {
        cancel_order->last->next = NULL;
        pizzeria->selected = NULL;
    } else if (cancel_order->last == NULL) {
        cancel_order->next->last = NULL;
        pizzeria->orders = cancel_order->next;
        pizzeria->selected = pizzeria->orders;
    } else {
        cancel_order->next->last = cancel_order->last;
        cancel_order->last->next = cancel_order->next;
        pizzeria->selected = cancel_order->next;
    }
    pizzeria->order_number--;

    // free the cancel order's ingredient part and free cancel order
    struct ingredient *cancel_ingredient = cancel_order->ingredient;
    while (cancel_ingredient != NULL) {
        struct ingredient *temp = cancel_ingredient;
        cancel_ingredient = cancel_ingredient->next;
        free(temp);
    }

    free(cancel_order);
    return SUCCESS;
}

void free_pizzeria(struct pizzeria *pizzeria) {

    if (pizzeria == NULL) return;

    // free the pizzeria structure's sock part
    struct ingredient *free_stock = pizzeria->stock;
    while (free_stock != NULL) {
        struct ingredient *temp_stock = free_stock;
        free_stock = free_stock->next;
        free(temp_stock);
    }

    // free the pizzeria structure's order part
    struct order *free_order = pizzeria->orders;
    while (free_order != NULL) {
        struct order *temp_order = free_order;
        struct ingredient *free_ingredient = free_order->ingredient;
        while (free_ingredient != NULL) {
            struct ingredient *temp_ingredient = free_ingredient;
            free_ingredient = free_ingredient->next;
            free(temp_ingredient);
        }
        free_order = free_order->next;
        free(temp_order);
    }

    // free the pizzeria structure
    free(pizzeria);

}

int refill_stock(
    struct pizzeria *pizzeria,
    char *ingredient_name,
    int amount,
    double price
) {

    if (price < 0) return INVALID_PRICE;
    if (amount <= 0) return INVALID_AMOUNT;

    struct ingredient *new_stock = malloc(sizeof(struct ingredient));
    if (new_stock == NULL) {
        fprintf(stderr, "error: out of memory\n");
        exit(EXIT_FAILURE);
    }

    // set the structure's information
    copy_char(new_stock->name, ingredient_name);
    new_stock->amount = amount;
    new_stock->price = price;
    new_stock->next = NULL;

    // insert the new stock in alphabetical order, if there is a stock,
    // add the newly added amount, free the newly created stock
    if (pizzeria->stock == NULL) {
        pizzeria->stock = new_stock;
    } else {
        struct ingredient *add_stock = pizzeria->stock;
        for (; add_stock != NULL; add_stock = add_stock->next) {
            if (strcmp(ingredient_name, add_stock->name) < 0) {
                new_stock->next = pizzeria->stock;
                pizzeria->stock = new_stock;
                break;
            }
            if (strcmp(ingredient_name, add_stock->name) > 0 &&
                add_stock->next == NULL) {
                add_stock->next = new_stock;
                break;
            }
            if (strcmp(ingredient_name, add_stock->name) > 0 &&
                strcmp(ingredient_name, add_stock->next->name) < 0) {
                new_stock->next = add_stock->next;
                add_stock->next = new_stock;
                break;
            }
            if (strcmp(ingredient_name, add_stock->name) == 0) {
                add_stock->amount += amount;
                free(new_stock);
                break;
            }
        }
    }

    return SUCCESS;
}

void print_stock(struct pizzeria *pizzeria) {

    printf("The stock contains:\n");

    struct ingredient *print_stock = pizzeria->stock;
    for (; print_stock != NULL; print_stock = print_stock->next)
        print_ingredient(print_stock->name, print_stock->amount, print_stock->price);

}

int can_complete_order(struct pizzeria *pizzeria) {

    if (pizzeria->selected == NULL || pizzeria->selected->ingredient == NULL)
        return INVALID_ORDER;

    // compare between stock amount and requirement, if small, cannot complete,
    // or, return success
    struct ingredient *temp_ingredient = pizzeria->selected->ingredient;
    for (; temp_ingredient != NULL; temp_ingredient = temp_ingredient->next) {
        struct ingredient *temp_stock = pizzeria->stock;
        int loop = 0;
        for (; temp_stock != NULL; temp_stock = temp_stock->next) {
            if (strcmp(temp_ingredient->name, temp_stock->name) == 0 &&
                temp_ingredient->amount > temp_stock->amount) {
                return INSUFFICIENT_STOCK;
            } else if (strcmp(temp_ingredient->name, temp_stock->name) == 0 &&
                       temp_ingredient->amount <= temp_stock->amount) {
                loop = 1;
                break;
            }
        }
        if (loop == 0) return INSUFFICIENT_STOCK;
    }

    return SUCCESS;
}

////////////////////////////////////////////////////////////////////////
//                         Stage 4 Functions                          //
////////////////////////////////////////////////////////////////////////

int complete_order(struct pizzeria *pizzeria) {

    if (pizzeria->selected == NULL || pizzeria->selected->ingredient == NULL)
        return INVALID_ORDER;

    // confirm whether the stock cannot finish the order, if yes, reduce the stock;
    // if not, return directly
    int complete = can_complete_order(pizzeria);
    if (complete != SUCCESS) return complete;

    // all situation is the stock larger than or equal with the requirement, if equal,
    // delete tht stock, or reduce the amount
    struct ingredient *temp_ingredient = pizzeria->selected->ingredient;
    for (; temp_ingredient != NULL; temp_ingredient = temp_ingredient->next) {
        struct ingredient *temp_stock = pizzeria->stock;

        for (; temp_stock != NULL; temp_stock = temp_stock->next) {
            if (strcmp(temp_ingredient->name, temp_stock->name) == 0 &&
                       temp_ingredient->amount < temp_stock->amount) {
                temp_stock->amount -= temp_ingredient->amount;
                break;
            } else if (strcmp(temp_ingredient->name, temp_stock->name) == 0 &&
                       temp_ingredient->amount == temp_stock->amount) {
                delete_stock(pizzeria, temp_stock);
                break;
            }
        }
    }

    // use the cancel_order function to finish the selected order
    cancel_order(pizzeria);

    return SUCCESS;
}

int save_ingredients(struct pizzeria *pizzeria, char *file_name) {
    if (pizzeria->selected == NULL) return INVALID_ORDER;

    char save_char[MAX_CHARACTER];
    int position = 0;

    // collect all the content in a string save
    struct ingredient *sprint_ingredient = pizzeria->selected->ingredient;
    for (int loop = 0; loop < MAX_INGREDIENT && sprint_ingredient != NULL; loop++,
            sprint_ingredient = sprint_ingredient->next) {
        char temp_char[MAX_CHARACTER];
        sprintf(temp_char, "%s: %d @ $%.2lf\n", sprint_ingredient->name,
                sprint_ingredient->amount, sprint_ingredient->price);
        for (int loop_char = 0; temp_char[loop_char] != '\0'; loop_char++, position++)
            save_char[position] = temp_char[loop_char];
    }
    save_char[position] = '\0';
    save_string(file_name, save_char);

    return SUCCESS;
}

int load_ingredients(struct pizzeria *pizzeria, char *file_name) {

    if (pizzeria->selected == NULL) return INVALID_ORDER;

    char *load_char = load_string(file_name);
    int position = 0;

    // get all important information from the file， read line by line('\n') and
    // stop at ('\0')
    while (load_char[position] != '\0') {
        char temp_char[MAX_SIZE];
        int loop = 0;
        for (; load_char[position] != '\n'; loop++, position++)
            temp_char[loop] = load_char[position];
        temp_char[loop] = '\0';
        position++;

        char name[MAX_SIZE];
        int amount;

        char temp_char1[MAX_SIZE];
        char temp_char2[MAX_SIZE];

        sscanf(temp_char, "%s %d %s %s", name, &amount, temp_char1, temp_char2);

        int temp_position = 0;
        for (; name[temp_position] != ':'; temp_position++);
        name[temp_position] = '\0';

        for (temp_position = 1; temp_char2[temp_position] != '\0'; temp_position++) {
            temp_char1[temp_position - 1] = temp_char2[temp_position];
        }
        temp_char1[temp_position - 1] = '\0';

        add_ingredient(pizzeria, name, amount, atof(temp_char1));

    }

    free(load_char);

    return SUCCESS;
}

////////////////////////////////////////////////////////////////////////
//               HELPER FUNCTIONS - Add your own here                 //
////////////////////////////////////////////////////////////////////////

// copy the string such as pizzeria's name, customer's name to struct's string part
void copy_char(char paste[MAX_SIZE], char *copy) {
    int loop = 0;
    for (; copy[loop] != '\0'; loop++) {
        paste[loop] = copy[loop];
    }
    paste[loop] = '\0';
}

// help when the amount of stock equal 0, delete this node
void delete_stock(struct pizzeria *pizzeria, struct ingredient *delete_stock) {
    struct ingredient *temp_stock = pizzeria->stock;
    for (; temp_stock != NULL; temp_stock = temp_stock->next) {
        if (temp_stock == delete_stock) {
            pizzeria->stock = temp_stock->next;
            break;
        }
        if (temp_stock->next == delete_stock) {
            temp_stock->next = delete_stock->next;
            break;
        }
    }
    free(delete_stock);
}

// Prints a single order
//
// `print_order` will be given the parameters:
// - `num` -- the integer that represents which order it is sequentially.
// - `customer` -- the name of the customer for that order.
// - `pizza_name` -- the pizza the customer ordered.
// - `price` -- the price the customer is paying for the pizza.
// - `time_allowed` -- the time the customer will wait for the order.
//
// `print_order` assumes all parameters are valid.
//
// `print_order` returns nothing.
//
// This will be needed for Stage 1.
void print_order(
    int num,
    char *customer,
    char *pizza_name,
    double price,
    int time_allowed
) {

    printf("%02d: %s ordered a %s pizza ($%.2lf) due in %d minutes.\n",
        num, customer, pizza_name, price, time_allowed);

    return;
}

// Prints a single ingredient
//
// `print_ingredient` will be given the parameters:
// - `name` -- the string which contains the ingredient's name.
// - `amount` -- how many of the ingredient we either need or have.
// - `price` -- the price the ingredient costs.
//
// `print_ingredient` assumes all parameters are valid.
//
// `print_ingredient` returns nothing.
//
// This will be needed for Stage 2.
void print_ingredient(char *name, int amount, double price) {
    printf("    %s: %d @ $%.2lf\n", name, amount, price);
}
