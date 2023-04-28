#include "opt-synchprobs.h"
#include "kitchen.h"
#include <types.h>
#include <lib.h>
#include <test.h>
#include <thread.h>
#include <synch.h>

/* THIS FILE WILL BE REPLACED IN AUTOMARKING SO YOU SHOULD NOT RELY ON
   ANY CHANGES YOU MAKE HERE FOR PERSONAL TESTING */

#define NUM_DINERS 20
#define NUM_SERVES 10
/* 
 * We use a semaphore to wait for threads to finish
 */
static struct semaphore *finished;

/* keep some counters to check the behaviour of your implementation */ 
static int served;
static int servings_remaining;

static void eat(void)
{
        /* Yum, Yum :-) */
        /* Sanity check the pot */
        if (servings_remaining < 0){
                panic("Pot has negative servings remaining");
        }
        if (servings_remaining > POTSIZE_IN_SERVES) {
                panic("Pot has overflowed");
        }       
}

void get_serving_from_pot(void)
{
        if (servings_remaining <= 0) {
                panic("Attempting to fill bowl from empty pot");
        }
        served++;
        servings_remaining--;
};

void cook_soup_in_pot(void)
{
        if (servings_remaining != 0) {
                panic("Can only cook in an empty pot");
        }
        servings_remaining += POTSIZE_IN_SERVES;
};


static void cooking_thread(void * unusedpointer, unsigned long threadnumber)
{
        /*
         * Avoid unused variable warnings.
         */
        (void) unusedpointer; 
        (void) threadnumber;
        int i;


        int pots_to_cook = (NUM_DINERS * NUM_SERVES + POTSIZE_IN_SERVES - 1) / POTSIZE_IN_SERVES; 

        for (i = 0; i < pots_to_cook; i++) {
                do_cooking();
        }

        /* signal the top-level tester thread we have finished and
           then exit */
        V(finished);
        thread_exit();
}

static void dining_thread(void * unusedpointer, unsigned long threadnumber)
{
       /*
        * Avoid unused variable warnings.
        */
        (void) unusedpointer; 
        (void) threadnumber;

        int i;

        for (i = 0; i <  NUM_SERVES; i++) {
                fill_bowl();
                eat();
        }                


        /* signal the top-level tester thread we have finished and
           then exit */
        V(finished);
        thread_exit();
}


int kitchen_tester (int data1, char **data2)
{
        int index, error;

        /*
         * Avoid unused variable warnings from the compiler.
         */
        (void) data1;
        (void) data2;

        served = 0;
        servings_remaining = 0;
        
        /* create a semaphore to allow main thread to wait on workers */
        
        finished = sem_create("finished", 0);
        
        if (finished == NULL) {
                panic("kitchen_tester: sem create failed");
        }
        
        /* call the initialiser for the kitchen */
        
        error = initialise_kitchen();
        
        if (error) {
                panic("kitchen_tester: initialise_kitchen failed");
        }
        
        /*
         * Start dining threads.
         */
        
        kprintf("Starting %d dining threads who eat %d serves each\n",
                NUM_DINERS, NUM_SERVES);
        
        for (index = 0; index < NUM_DINERS; index++) {
                
                error = thread_fork("dining thread", NULL, &dining_thread, NULL, index);
                
                /*
                 * panic() on error as we can't progress if we can't
                 * create threads.
                 */

                if (error) {
                        panic("dining thread: thread_fork failed: %s\n",
                              strerror(error));
                }
        }
        
        kprintf("Starting cooking thread\n");
        error = thread_fork("cook thread", NULL, &cooking_thread, NULL, 0);
        
        /*
         * panic() on error as we can't progress if we can't create thread.
         */
        
        if (error) {
                panic("cooking thread: thread_fork failed: %s\n",
                      strerror(error));
        }
        
        /* 
         * Wait until the threads complete by waiting on the semaphore
         * NUM_DINERS times.
         */
        
        for (index = 0; index < NUM_DINERS; index++) {
                P(finished);
        }

        /* Wait for one more (the cook thread) */
        P(finished);
        
        /* call the cleanup code */
        cleanup_kitchen();
        
        kprintf("The total number of servings served was %d (expected %d)\n",
                served, NUM_DINERS * NUM_SERVES); 
        
        /* clean up the semaphore we allocated earlier */
        sem_destroy(finished);
        return 0;
}

