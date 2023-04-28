#ifndef COUNTER_H
#define COUNTER_H

extern void counter_increment(void);
extern void counter_decrement(void) ;      
extern int counter_initialise(int val);
extern int counter_read_and_destroy(void);

#endif
