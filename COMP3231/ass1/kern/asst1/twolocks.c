#include "opt-synchprobs.h"
#include <types.h>
#include <lib.h>
#include <test.h>
#include <thread.h>
#include <synch.h>
#include "twolocks.h"

/********************************************************************************
 Document your resource order here. 
********************************************************************************/



/* declare (local to this file) pointers to the synch variables that
   we will allocate later */

static struct lock *locka, *lockb;
static struct semaphore *finished;

/* a constant indicating how many times the locking loops go round */
#define NUM_LOOPS 1000


/* Bill, Ben, Bob and Bruce are four threads that simply spin for a while,
   acquiring and releasing locks */

static void bill(void * unusedpointer, unsigned long unusedint)
{
        int i;
        (void) unusedpointer;
        (void) unusedint;

        kprintf("Hi, I'm Bill\n");

        for (i = 0; i < NUM_LOOPS; i++) {
                
                lock_acquire(lockb);
                
                holds_lockb();          /* Critical section */
                
                lock_release(lockb);

                lock_acquire(locka);
                lock_release(locka);
                lock_acquire(lockb);
                lock_acquire(locka);

                                        /* Bill now holds both locks and can do
                                        what ever bill needs to do while holding
                                        the locks */
                holds_locka_and_b();
                
                lock_release(lockb);
                lock_release(locka);
        }

        kprintf("Bill says 'bye'\n");
        V(finished); /* indicate to the parent thread Bill has
                        finished */
}

static void bruce(void * unusedpointer, unsigned long unusedint)
{
        int i;
        (void) unusedpointer;
        (void) unusedint;

        kprintf("Hi, I'm Bruce\n");

        for (i = 0; i < NUM_LOOPS; i++) {
                
                lock_acquire(lockb);
                
                holds_lockb();          /* Critical section */
                
                lock_release(lockb);


        }

        kprintf("Bruce says 'bye'\n");
        V(finished); /* indicate to the parent thread Bruce has
                        finished */
}

static void ben(void * unusedpointer, unsigned long unusedint)
{
        int i;
        (void) unusedpointer;
        (void) unusedint;

        kprintf("Hi, I'm Ben\n");

        for (i = 0; i < NUM_LOOPS; i++) {
                
                lock_acquire(locka);

                holds_locka();          /* Critical section */
                
                lock_release(locka);

                lock_acquire(lockb);
                lock_acquire(locka);

                                        /* Ben now holds both locks and can do
                                         what ever ben needs to do while holding
                                         the locks */
                holds_locka_and_b();
                
                lock_release(locka);
                lock_release(lockb);
        }

        kprintf("Ben says 'bye'\n");
        V(finished); /* indicate to the parent thread Bill has
                        finished */
}

static void bob(void * unusedpointer, unsigned long unusedint)
{

        int i;
        (void) unusedpointer;
        (void) unusedint;
        
        kprintf("Hi, I'm Bob\n");

        for (i = 0; i < NUM_LOOPS; i++) {
                lock_acquire(locka);

                holds_locka();          /* Critical section */
                
                lock_release(locka);

        }

        kprintf("Bob says 'bye'\n");
        V(finished); /* indicate to the parent thread Bob has
                        finished */

}


int twolocks (int data1, char ** data2)
{
        int error;
        /*
         * Avoid unused variable warnings.
         */
        (void) data1;
        (void) data2;

        kprintf("Locking frenzy starting up\n");


        finished = sem_create("finished", 0);
        KASSERT(finished != 0); /* KASSERT panics if the condition is
                                   false. Okay for development, but
                                   production code should handle this
                                   better. */

        locka = lock_create("lock_a");
        KASSERT(locka != 0);

        lockb = lock_create("lock_b");
        KASSERT(lockb != 0);



        error = thread_fork("bill thread", NULL, &bill, NULL, 0); /* start
                                                                     Bill */

        /*
         * panic() on error. One should not panic for normal system
         * calls, but it is okay for this assignment if the error is
         * unrecoverable.
         */

        if (error) {
                panic("bill: thread_fork failed: %s\n", strerror(error));
        }


        error = thread_fork("ben thread", NULL, &ben, NULL, 0); /* start
                                                                   Ben */

        /*
         * panic() on error.
         */

        if (error) {
                panic("ben: thread_fork failed: %s\n", strerror(error));
        }

        error = thread_fork("bob thread", NULL, &bob, NULL, 0); /* start
                                                                   Bob */

        /*
         * panic() on error.
         */

        if (error) {
                panic("bob: thread_fork failed: %s\n", strerror(error));
        }

        error = thread_fork("bruce thread", NULL, &bruce, NULL, 0); /* start
                                                                   Bruce */

        /*
         * panic() on error.
         */

        if (error) {
                panic("bruce: thread_fork failed: %s\n", strerror(error));
        }

        /* Wait for the threads to signal finished */
        P(finished);
        P(finished);
        P(finished);
        P(finished);

        kprintf("Locking frenzy finished\n");

        /* Now clean up the previously created semaphores */
        lock_destroy(locka);
        lock_destroy(lockb);
        sem_destroy(finished);

        return 0;
}
