#include "opt-synchprobs.h"
#include "counter.h"
#include <types.h>
#include <lib.h>
#include <test.h>
#include <thread.h>
#include <synch.h>

/* THIS FILE WILL BE REPLACED IN AUTOMARKING SO YOU SHOULD NOT RELY ON ANY CHANGES
   YOU MAKE HERE FOR PERSONAL TESTING */

enum {
        NINCREMENTERS = 10,        /* the number of incrementer threads */
        NINCS   = 1000,            /* the number of increments performed by each thread */
};


/* 
 * We use a semaphore to wait for threads to finish
 */
struct semaphore *finished;


/*
 *  Each thread simply keeps incrementing the counter until it
 *  performs the required number of increments
 */

static void incrementer_thread(void * unusedpointer, unsigned long threadnumber)
{

        int i;
        /*
         * Avoid unused variable warnings.
         */
        (void) unusedpointer; 
        (void) threadnumber;

        for (i = 0; i < NINCS; i++) {
                /* loop doing increments until we perform the required number */
                counter_increment();
        }

        /* signal the top-level tester thread we have finished and
           then exit */
        V(finished);

        thread_exit();
}

/*
 * counter_tester()
 *
 * This function:
 *
 * + Initialises the counter by calling the initialiser function
 * + Creates a semaphore to wait for threads to complete
 * + Starts the defined number of threads
 * + waits, prints statistics, cleans up, and exits
 */

int counter_tester (int data1, char **data2)
{
        int index, error, final_count;

        /*
         * Avoid unused variable warnings from the compiler.
         */
        (void) data1;
        (void) data2;

        /* create a semaphore to allow main thread to wait on workers */

        finished = sem_create("finished", 0);

        if (finished == NULL) {
                panic("counter_tester: sem create failed");
        }

        /* call the initialiser in the counter interface */
        
        error = counter_initialise(0);
        
        if (error) {
                panic("counter_tester: initialise counter failed");
        }
        
        /*
         * Start NINCREMENTER  threads.
         */

        kprintf("Starting %d incrementer threads\n", NINCREMENTERS);

        for (index = 0; index < NINCREMENTERS; index++) {
                
                error = thread_fork("inc thread", NULL, &incrementer_thread, NULL, index);

                /*
                 * panic() on error as we can't progress if we can't create threads.
                 */

                if (error) {
                        panic("inc thread: thread_fork failed: %s\n",
                              strerror(error));
                }
        }


        /* 
         * Wait until the threads complete by waiting on the semaphore
         * NINCREMENTER times.
         */

        for (index = 0; index < NINCREMENTERS; index++) {
                P(finished);
        }


        /* call the cleanup code for the counter */
        
        final_count = counter_read_and_destroy();
        
        kprintf("The final count value was %d (expected %d)\n", final_count, NINCREMENTERS * NINCS);

        /* clean up the semaphore we allocated earlier */
        sem_destroy(finished);
        return 0;
}

