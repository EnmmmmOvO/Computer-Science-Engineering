//
// DO NOT CHANGE THIS FILE
//
// You do not submit this file. This file is not marked.
// If you think you need to change this file you have
// misunderstood the assignment - ask in the course forum.
//
// Assignment 2 DPST1091: CS Pizzeria
// pizzeria.h
//
// YOU MUST NOT CHANGE THIS FILE
//
// Version 1.0.0: Release

#ifndef _PIZZERIA_H_
#define _PIZZERIA_H_

// Every string passed in will be less than MAX_STR_LENGTH characters long.
#define MAX_STR_LENGTH 64

#define SUCCESS 0
#define INVALID_PRICE 1
#define INVALID_TIME 2
#define INVALID_ORDER 4
#define INVALID_AMOUNT 5
#define INSUFFICIENT_STOCK 6
#define INVALID_CALL -1

// Stage 4 use only.
#define MAX_SAVE_LENGTH 8096

////////////////////////////////////////////////////////////////////////
//                         Stage 1 Functions                          //
////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////
// Create a new Pizzeria and return a pointer to it.
//
// The pointer is pointing to the memory allocated by `malloc` and it is
// the responsibility of the program that called the function (caller)
// to free the memory once they're done using the `free_pizzeria` function
// implemented in Stage 3.
//
// Part of this function has been implemented but it will need to be
// modified if you change the provided struct pizzeria.
//
struct pizzeria *create_pizzeria();

////////////////////////////////////////////////////////////////////////
// INSERT ORDER INTO PIZZERIA - Command 'o'
//
// Add a new Order to the Pizzeria and return an int indicating the
// resulting status of the new Order.
//
// The new Order should be added to the end of the Pizzeria's list of
// Orders. This means that you should add the Order directly after the
// most recent Order added.
//
// `add_order` will be given the parameters:
// - `pizzeria` -- a pointer to a struct pizzeria created by
//   `create_pizzeria`.
// - `customer` -- a string, which contains the name of the customer
//   for the order.
// - `pizza_name` -- a string, which contains the name of the pizza for
//   the order.
// - `price` -- a double, which indicates the cost of the order the
//   customer must pay. An invalid `price` may be passed in and an
//   invalid `price` is a double less than 0.
// - `time_allowed` -- an int, which indicates the time when the
//   customer expects the order. If `time_allowed` is 15, this means
//   the customer expects the order in 15 minutes. An invalid
//   `time_allowed` may be passed in and an invalid `time_allowed`
//   is an int less than or equal to 0.
//
// `add_order` will return (in order of precedence):
// - `INVALID_PRICE` -- if the price is invalid (negative).
// - `INVALID_TIME` -- if the time_allowed is invalid (non-positive).
// - `SUCCESS` -- if the Order has been successfully added to the Pizzeria.
//
// ASSUMPTIONS
// - `pizzeria` will always be a valid pointer and never be NULL.
// - `customer` will always be a valid string.
// - `pizza_name` will always be a valid string.
//
int add_order(
    struct pizzeria *pizzeria,
    char *customer,
    char *pizza_name,
    double price,
    int time_allowed
);

////////////////////////////////////////////////////////////////////////
// PRINT ALL ORDERS OF THE PIZZERIA - Command 'p'
//
// Print all orders of the Pizzeria given and return nothing.
//
// `print_all_orders` should print out each order separated by a
// newline ('\n'). Printing each order should be done by calling the
// provided `print_order` function.
//
// The orders should be printed in the order they were added to the Pizzeria.
//
// For a pizzeria containing (in order):
// - An order with customer name "Tom", pizza name "Pepperoni", price
//   8.70 and time allowed 20 and
// - An order with customer name "Shrey" and pizza name "Pineapple",
//   price 7.50 and time allowed 15,
//
// `print_all_orders` should print:
// "01: Tom ordered a Pepperoni pizza ($8.70) due in 20 minutes.\n
//  02: Shrey ordered a Pineapple pizza ($7.50) due in 15 minutes.\n"
//
// `print_all_orders` will be given the parameters:
// - `pizzeria` -- a pointer to a struct pizzeria created by
//   `create_pizzeria` which may or may not have orders inside.
//
// `print_all_orders` will return nothing.
//
// ASSUMPTIONS
// - `pizzeria` will always be a valid pointer and never be NULL.
//
void print_all_orders(struct pizzeria *pizzeria);

////////////////////////////////////////////////////////////////////////
// GET THE NEXT DEADLINE - Command '!'
//
// Return the shortest `time_allowed` among the orders.
//
// For example, if in the linked list of orders, we have:
// - Order with `time_allowed` of 20
// - Order with `time_allowed` of 15
// - Order with `time_allowed` of 30,
// This function should return 15.
//
// `next_deadline` will be given the parameters:
// - `pizzeria` -- a pointer to a struct pizzeria created by
//   `create_pizzeria` which may or may not have orders inside.
//
// `next_deadline` will return (in order of precedence):
// - `INVALID_CALL` -- if there are no orders in the pizzeria.
// - the shortest `time_allowed` among the orders.
//
// ASSUMPTIONS
// - `pizzeria` will always be a valid pointer and never be NULL.
//
int next_deadline(struct pizzeria *pizzeria);

////////////////////////////////////////////////////////////////////////
//                         Stage 2 Functions                          //
////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////
// SELECT THE NEXT ORDER IN THE PIZZERIA - Command '>'
//
// Given a Pizzeria, sets the selected order to the order after the
// currently selected order.
//
// For example, if the current selected order below is the second one
//
//            [order]->[order]->[order]->[order]->X
//                        ^
//                     selected
//
// Then, this command will move the selected to the next order after it
//
//            [order]->[order]->[order]->[order]->X
//                                 ^
//                              selected
//
// If this command is input again, the last order will be selected
//
//            [order]->[order]->[order]->[order]->X
//                                          ^
//                                       selected
//
// If there is no selected order currently and at least one order exists, then
// the first order in the pizzeria will be selected after this function runs.
//
// If the last order is selected and this function runs then no order will be
// selected afterwards.
//
// `select_next_order` will be given the parameters:
// - `pizzeria` -- a pointer to a struct pizzeria created by
//   `create_pizzeria` which may or may not have orders inside.
//
// ASSUMPTIONS
// - `pizzeria` will always be a valid pointer and never be NULL.
// - This function should do nothing in an empty pizzeria
//
void select_next_order(struct pizzeria *pizzeria);

////////////////////////////////////////////////////////////////////////
// SELECT THE PREVIOUS ORDER IN THE PIZZERIA - Command '<'
//
// Given a Pizzeria, sets the selected order to the order before the
// currently selected order.
//
// For example, if the current selected order below is the last one
//
//            [order]->[order]->[order]->[order]->X
//                                          ^
//                                       selected
//
// Then, this command will move the selected to the one before it
//
//            [order]->[order]->[order]->[order]->X
//                                 ^
//                              selected
//
// If this command is input again, the second order will be selected
//
//            [order]->[order]->[order]->[order]->X
//                        ^
//                     selected
//
// If there is no selected order currently and at least one order exists, then
// the last order in the pizzeria will be selected after this function runs.
//
// If the first order is selected and this function runs then no order will be
// selected afterwards.
//
// `select_previous_order` will be given the parameters:
// - `pizzeria` -- a pointer to a struct pizzeria created by
//   `create_pizzeria` which may or may not have orders inside.
//
// ASSUMPTIONS
// - `pizzeria` will always be a valid pointer and never be NULL.
// - This function should do nothing in an empty pizzeria
//
void select_previous_order(struct pizzeria *pizzeria);

////////////////////////////////////////////////////////////////////////
// PRINT DETAILS OF THE SELECTED ORDER
//
// Given a Pizzeria, prints the selected order's details and its list of
// ingredients. To print the list of ingredients, use the supplied
// `print_ingredient` function.
//
// When there is no selected order, `print_selected_order` should print:
//
// "\nNo selected order.\n"
//
// If the selected order is Tom's Pepperoni pizza ($8.70) due in 20 minutes,
// `print_selected_order` should print:
//
// "\nThe selected order is Tom's Pepperoni pizza ($8.70) due in 20 minutes.\n"
// and then the ingredients line by line using the `print_ingredient` function.
//
// `print_selected_order` will be given the parameters:
// - `pizzeria` -- a pointer to a struct pizzeria created by
//   `create_pizzeria` which may or may not have orders inside.
//
// `print_selected_order` will return nothing.
//
// ASSUMPTIONS
// - `pizzeria` will always be a valid pointer and never be NULL.
//
void print_selected_order(struct pizzeria *pizzeria);

////////////////////////////////////////////////////////////////////////
// ADD INGREDIENT TO THE SELECTED ORDER - Command 'i'
//
// Given a Pizzeria, adds an ingredient to the currently selected order. This
// ingredient must be inserted in alphabetical order.
//
// For example, given the selected order with the named ingredients:
//                                 X
//                                 ^
//                                 |
//                           [Tomato_sauce]
//                                 ^
//                                 |
//                            [Pepperoni]
//                                 ^
//                                 |
//                           [Black_olives]
//                                 ^
//                                 |
//                              [order]
//
// If a new ingredient of name 'Mushrooms' were to be added, it would be
// inserted between 'Black_olives' and 'Pepperoni' as it fits between them
// alphabetically, resulting in:
//
//                                 X
//                                 ^
//                                 |
//                           [Tomato-sauce]
//                                 ^
//                                 |
//                            [Pepperoni]
//                                 ^
//                                 |
// ----> // Newly inserted!   [Mushrooms]
//                                 ^
//                                 |
//                           [Black-olives]
//                                 ^
//                                 |
//                              [order]
//
// This function can take in the same ingredient twice, if such an event
// occurs then the `amount` of the first instance of this ingredient should
// be incremented by the new amount given.
//
// For example, if "Mushrooms" was added twice to the selected order with an
// amount of 3 then 5, there should only be one `Ingredient` named "Mushrooms"
// that exists in the selected order, but it will now have an amount of 8.
//
// The `price` parameter refers to the price of 1 of the given ingredient, it's
// value has no correlation with the amount of this ingredient.
//
// You will never be asked to insert two ingredients of the same name but with
// different prices.
//
// `add_ingredient` will be given the parameters:
// - `pizzeria` -- a pointer to a struct pizzeria created by
//   `create_pizzeria` which may or may not have orders inside.
// - `ingredient_name` -- a string containing the name of the ingredient.
// - `amount` -- The amount of the ingredient required for the order.
// - `price` -- The price of ONE of this ingredient (not related to `amount`).
//
// `add_ingredient` will return (in order of precedence):
// - `INVALID_ORDER` -- if there is no selected order in the pizzeria.
// - `INVALID_PRICE` -- if the price given is negative.
// - `INVALID_AMOUNT` -- if the amount given is not a non-zero positive integer.
// - `SUCCESS` -- otherwise.
//
// ASSUMPTIONS
// - `pizzeria` will always be a valid pointer and never be NULL.
// - `ingredient_name` will always be a valid string.
// - All ingredients of the same name will have the same price.
//
int add_ingredient(
    struct pizzeria *pizzeria,
    char *ingredient_name,
    int amount,
    double price
);

////////////////////////////////////////////////////////////////////////
// CALCULATE TOTAL PROFIT TO BE MADE FROM SELECTED ORDER - Command 't'
//
// Given a Pizzeria, calculates how much profit is to be made from the currently
// selected order.
//
// All orders have a sell price. This is the price that the order actually sold
// for, to the customer. Each order also has a list of ingredients with
// individual prices each. These prices are what the Pizzeria bought them at
// per unit.
//
// This function calculates the profit from an order by getting the difference
// between the order price and the sum of the ingredient price.
//
// An important note, for ingredients, they have price per unit but also an
// amount. So when there is an ingredient, "Mushrooms" with `amount` = 5 and
// `price` = 2, then "Mushrooms" costs 5 * 2 = $10 for that order.
//
// Here is an example of calculating total profit:
//
//                                 X
//                                 ^
//                                 |
//    [Ingredient: name = "Brie-cheese", amount = 3, price = 3.0]
//                                 ^
//                                 |
//     [Ingredient: name = "Pepperoni", amount = 5, price = 1.5]
//                                 ^
//                                 |
//    [Ingredient: name = "Black-olives", amount = 10, price = 0.5]
//                                 ^
//                                 |
//                     [order 1: price = 30.0]
//
// Looking at this order,
// Price of order for customer = $30.0
// Price of ingredients = (10 * 0.5) + (5 * 1.5) + (3 * 3.0) = $21.5
//
// And so,
// Profit = Price of order for customer - Price of ingredients = 30 - 21.5 = $8.5
//
// `calculate_total_profit` will be given the parameters:
// - `pizzeria` -- a pointer to a struct pizzeria created by
//   `create_pizzeria` which may or may not have orders inside.
//
// `calculate_total_profit` will return (in order of precedence):
// - `INVALID_ORDER` -- if there is no selected order in the pizzeria.
// - The profit to be received from the selected order.
//
// ASSUMPTIONS
// - `pizzeria` will always be a valid pointer and never be NULL.
// - The return value will never be 4.00 (will cause issues with `INVALID_ORDER`)
//
double calculate_total_profit(struct pizzeria *pizzeria);

////////////////////////////////////////////////////////////////////////
//                         Stage 3 Functions                          //
////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////
// CANCEL ORDER IN PIZZERIA - Command 'c'
//
// Cancel the currently selected order in the pizzeria.
//
// Call free on the selected order, and free all associated memory.
// You will need to free the memory associated with the ingredients
// before freeing the order itself.
//
// If `cancel_order` is called on this linked list of orders for
//
// [order1]->[order3]->[order4]->[order5]->X
//              ^
//              |
//           selected
//
// Afterwards, the linked list should be:
//
// [order1]->[order4]->[order5]->X
//              ^
//              |
//           selected
//
// Upon cancelling an order, the selected order will be the next one in the
// list. If the last order is cancelled then there will be no selected order.
//
// `cancel_order` will be given the parameters:
// - `pizzeria` -- a pointer to a struct pizzeria which may or may not
//   have orders inside.
//
// `cancel_order` will return:
// - `INVALID_ORDER` -- if no order is selected.
// - `SUCCESS` -- if the order was successfully cancelled.
//
// ASSUMPTIONS
// - `pizzeria` will always be a valid pointer and never be NULL.
//
int cancel_order(struct pizzeria *pizzeria);

////////////////////////////////////////////////////////////////////////
// FREE THE GIVEN PIZZERIA
//
// Call free on the given pizzeria, and free all associated memory. You will
// need to free the memory associated with the orders before freeing
// the pizzeria itself.
//
// `free_pizzeria` will be given the parameters:
// - `pizzeria` -- a pointer to a struct pizzeria which may or may not
//    have orders inside.
//
// `free_pizzeria` will return nothing.
//
// ASSUMPTIONS
// - `pizzeria` will always be a valid pointer and never be NULL.
//
void free_pizzeria(struct pizzeria *pizzeria);

////////////////////////////////////////////////////////////////////////
// REFILLS THE STOCK IN THE PIZZERIA - Command 'r'
//
// Given an ingredient and its information, refills this in the stock of
// the given Pizzeria
//
// `refill_stock` acts in the EXACT same way to `add_ingredient` but instead
// of adding this ingredient to the order, you are adding it to the overall
// stock of the Pizzeria.
//
// `refill_stock` will be given the parameters:
// - `pizzeria` -- a pointer to a struct pizzeria created by
//   `create_pizzeria` which may or may not have orders inside.
// - `ingredient_name` -- a string containing the name of the ingredient.
// - `amount` -- The amount of the ingredient required for the order.
// - `price` -- The price of ONE of this ingredient (not related to `amount`).
//
// `refill_stock` will return (in order of precedence):
// - `INVALID_PRICE` -- if the price given is negative.
// - `INVALID_AMOUNT` -- if the amount given is not a non-zero positive integer.
// - `SUCCESS` -- otherwise
//
// ASSUMPTIONS
// - `pizzeria` will always be a valid pointer and never be NULL.
// - All ingredients of the same name will have the same price.
// - `ingredient_name` will always be a valid string.
//
int refill_stock(
    struct pizzeria *pizzeria,
    char *ingredient_name,
    int amount,
    double price
);

////////////////////////////////////////////////////////////////////////
// PRINTS THE STOCK OF THE PIZZERIA  - Command 's'
//
// Print all ingredients of the stock in the Pizzeria given and return nothing.
//
// `print_stock` should print out each ingredient separated by a
// newline ('\n'). Printing each ingredient should be done by calling the
// provided `print_ingredient` function.
//
// The stock should be printed in the order they are in in the linked
// list.
//
// If the pizzeria contains no stock, only “The stock contains:\n”
// should be printed.
//
// `print_stock` will be given the parameters:
// - `pizzeria` -- a pointer to a struct pizzeria created by
//   `create_pizzeria` which may or may not have orders inside.
//
// `print_stock` will return nothing.
//
// ASSUMPTIONS
// - `pizzeria` will always be a valid pointer and never be NULL.
//
void print_stock(struct pizzeria *pizzeria);

////////////////////////////////////////////////////////////////////////
// DETERMINES IF AN ORDER CAN BE COMPLETED - Command '?'
//
// Given a Pizzeria determines if the currently selected order can be completed,
// determined by how much stock is available.
//
// Orders can only be deemed completable if all the ingredients required for
// said order exist in the Pizzeria stock including their amounts.
//
// For example, lets say that an order has:
//
// - 3 Capsicums
// - 1 Mozzarella cheese
// - 5 Mushrooms
// - 6 Slices of pepperoni
//
// And the stock has
//
// - 2 Capsicums
// - 20 Mozzarella cheese
// - 8 Mushrooms
// - 10 Pineapple
// - 4 Slices of pepperoni
//
// The order cannot be deemed completable as there is some stock missing.
// - 2 Slices of pepperoni and
// - 1 Capsicum
//
// `can_complete_order` will be given the parameters:
// - `pizzeria` -- a pointer to a struct pizzeria which may or may not
//   contain a selected order.
//
// `can_complete_order` will return:
// - `INVALID_ORDER` -- if there is no selected order or the order has no ingredients.
// - `INSUFFICIENT_STOCK` -- if the stock does not satisfy order requirements.
// - `SUCCESS` -- if the order can be completed
//
// ASSUMPTIONS
// - `pizzeria` will always be a valid pointer and never be NULL.
//
int can_complete_order(struct pizzeria *pizzeria);


////////////////////////////////////////////////////////////////////////
//                         Stage 4 Functions                          //
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
// ATTEMPT TO COMPLETE AN ORDER - Command '#'
//
// Given a Pizzeria, completes the selected order if possible.
//
// A successful completion can be done when there are enough ingredients in
// the stock to satisfy this order. This can be determined from the
// `can_complete_order` function.
//
// Upon completing an order, all ingredients used for said order are subtracted
// from the stock.
//
// This means, if the stock has 500 slices of pepperoni and an order is
// completed which requires 20 slice, the stock will now have 480 slices of
// pepperoni.
//
// If the order is completed and any ingredient used now has an amount of 0
// in the stock, it should be removed from the stock list.
//
// `complete_order` will be given the parameters:
// - `pizzeria` -- a pointer to a struct pizzeria which may or may not
//   contain a selected order.
//
// `can_complete_order` will return:
// - `INVALID_ORDER` -- if there is no selected order or the order has no ingredients.
// - `INSUFFICIENT_STOCK` -- if the stock does not satisfy order requirements.
// - `SUCCESS` -- if the order was completed.
//
// ASSUMPTIONS
// - `pizzeria` will always be a valid pointer and never be NULL.
//
int complete_order(struct pizzeria *pizzeria);

////////////////////////////////////////////////////////////////////////
// SAVES ALL INGREDIENTS IN THE SELECTED ORDER TO A FILE - Command 'S'
//
// Given a Pizzeria, saves the ingredients of the selected order
// to a file as a string.
//
// `save_ingredients` will be given the parameters:
// - `pizzeria` -- a pointer to a struct pizzeria which may or may not
//   contain a selected order.
// - `file_name` -- The name of the file to save the selected order in.
//
// `save_ingredients` will return:
// - `INVALID_ORDER` -- if there is no selected order.
// - `SUCCESS` -- if the save was successful.
//
// ASSUMPTIONS
// - `pizzeria` will always be a valid pointer and never be NULL.
// - `file_name` will always be a valid string.
// - There will be given no more than 16 ingredients in the order to save.
// - The saved string must be no longer than 8096 characters (including '\0').
//
int save_ingredients(struct pizzeria *pizzeria, char *file_name);

////////////////////////////////////////////////////////////////////////
// LOADS ALL INGREDIENTS FROM A FILE INTO THE SELECTED ORDER - Command 'L'
//
// Given a Pizzeria, loads the ingredients of a saved file `file_name` into the
// selected order. This file will always be one that has been saved from using
// the `save_ingredients` function.
//
// `load_ingredients` will be given the parameters:
// - `pizzeria` -- a pointer to a struct pizzeria which may or may not
//   contain a selected order.
// - `file_name` -- The name of the file to load the desired order from.
//
// `load_ingredients` will return:
// - `INVALID_ORDER` -- if there is no selected order.
// - `SUCCESS` -- if the load was successful.
//
// ASSUMPTIONS
// - `pizzeria` will always be a valid pointer and never be NULL.
// - `file_name` will always be a valid string and will always refer to a file
//               that has been saved with `save_ingredients()`.
// - The loaded string will contain 16 ingredients at most.
// - The loaded string will have 8096 characters at most (including '\0').
//
int load_ingredients(struct pizzeria *pizzeria, char *file_name);

#endif // _PIZZERIA_H_
