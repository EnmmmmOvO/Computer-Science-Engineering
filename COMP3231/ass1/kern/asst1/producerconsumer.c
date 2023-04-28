/* This file will contain your solution. Modify it as you wish. */
#include <types.h>
#include <lib.h>
#include <synch.h>
#include "producerconsumer.h"

/* Declare any variables you need here to keep track of and
   synchronise your bounded buffer. A sample declaration of a buffer is shown
   below. It is an array of pointers to items.
   
   You can change this if you choose another implementation. 
   However, your implementation should accept at least BUFFER_SIZE 
   prior to blocking
*/

#define BUFFLEN (BUFFER_SIZE + 1)

data_item_t * item_buffer[BUFFER_SIZE+1];



volatile int head, tail;
static struct cv *empty, *full;
static struct lock *lock;


/* consumer_receive() is called by a consumer to request more data. It
   should block on a sync primitive if no data is available in your
   buffer. It should not busy wait! */

data_item_t * consumer_receive(void)
{
        data_item_t * item;

        lock_acquire(lock);

        while(head == tail) cv_wait(empty, lock);

        item = item_buffer[tail];
        tail = (tail + 1) % BUFFLEN;
        
        cv_signal(full, lock);
        lock_release(lock);

        return item;
}

/* procucer_send() is called by a producer to store data in your
   bounded buffer.  It should block on a sync primitive if no space is
   available in your buffer. It should not busy wait!*/

void producer_send(data_item_t *item)
{
        lock_acquire(lock);
        while((head + 1) % BUFFLEN == tail)  cv_wait(full, lock);

        item_buffer[head] = item;
        head = (head + 1) % BUFFLEN;
        
        cv_signal(empty, lock);
        lock_release(lock);
}



/* Perform any initialisation (e.g. of global data) you need
   here. Note: You can panic if any allocation fails during setup */

void producerconsumer_startup(void)
{
        head = tail = 0;
        
        empty = cv_create("queue empty");
        if (empty == NULL) panic("First CV create fail!\n");

        full = cv_create("queue full");
        if (full == NULL) {
                cv_destroy(empty);
                panic("Second CV create fail!\n");
        }

        lock = lock_create("lock");
        if (lock == NULL) {
                cv_destroy(empty);
                cv_destroy(full);
                panic("Lock create fail!\n");
        }
}

/* Perform any clean-up you need here */
void producerconsumer_shutdown(void)
{
        cv_destroy(empty);
        cv_destroy(full);
        lock_destroy(lock);
}

