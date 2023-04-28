#include "opt-synchprobs.h"
#include "counter.h"
#include <types.h>
#include <kern/errno.h>
#include <lib.h>
#include <test.h>
#include <thread.h>
#include <synch.h>


/*
 * Declare the counter variable that all threads increment or decrement
 * via the interface provided here.
 *
 * Declaring it "volatile" instructs the compiler to always (re)read the
 * variable from memory and not to optimise by keeping the value in a process 
 * register and avoid memory references.
 *
 * NOTE: The volatile declaration is actually not needed for the provided code 
 * as the variable is only loaded once in each function.
 */

static volatile int the_counter;
static struct lock *countner_lock;

/*
 * ********************************************************************
 * INSERT ANY GLOBAL VARIABLES YOU REQUIRE HERE
 * ********************************************************************
 */

void counter_increment(void)
{
        lock_acquire(countner_lock);
        the_counter = the_counter + 1;
        lock_release(countner_lock);
}

void counter_decrement(void)
{
        lock_acquire(countner_lock);
        the_counter = the_counter - 1;
        lock_release(countner_lock);
}

int counter_initialise(int val)
{
        /*
         * ********************************************************************
         * INSERT ANY INITIALISATION CODE YOU REQUIRE HERE
         * ********************************************************************
         */
        
        
        /*
         * Return 0 to indicate success
         * Return non-zero to indicate error.
         * e.g. 
         * return ENOMEM
         * indicates an allocation failure to the caller 
         */
        the_counter = val;
        countner_lock = lock_create("countner lock");
        if (countner_lock == NULL) return ENOMEM;
        return 0;
}

int counter_read_and_destroy(void)
{
        /*
         * **********************************************************************
         * INSERT ANY CLEANUP CODE YOU REQUIRE HERE
         * **********************************************************************
         */
        lock_acquire(countner_lock);
        int result = the_counter;
        lock_release(countner_lock);

        lock_destroy(countner_lock);
        return result;
}
