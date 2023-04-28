#ifndef KITCHEN_H
#define KITCHEN_H

/*
 * This file will be replaced in testing, so you should not make any
 * changes made here.
 *
 * You can vary the size of the pot for testing purposes (we will in
 * our testing of your submission).
 */

#define POTSIZE_IN_SERVES 10
extern void get_serving_from_pot(void);
extern void cook_soup_in_pot(void);

extern int initialise_kitchen(void);
extern void cleanup_kitchen(void);

extern void do_cooking(void);
extern void fill_bowl(void);
#endif

