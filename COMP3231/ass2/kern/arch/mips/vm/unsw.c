/*
 * Copyright (c) 2000, 2001, 2002, 2003, 2004, 2005, 2008, 2009
 *	The President and Fellows of Harvard College.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE UNIVERSITY AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE UNIVERSITY OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

#include <types.h>
#include <lib.h>
#include <vm.h>
#include <mainbus.h>
#include <spinlock.h>

vaddr_t firstfree;   /* first free virtual address; set by start.S */

static paddr_t firstpaddr;  /* address of first free physical page */
static paddr_t lastpaddr;   /* one past end of last free physical page */



typedef struct ft_entry {
        unsigned allocated:1; /* the corresponding frame is allocated */
        unsigned not_last:1; /* the frame is part of a multiframe allocation */
} ft_entry_t;


static ft_entry_t * frame_table = NULL; /* base of frame table */
static uint32_t first_frame;
static uint32_t last_frame;

#define PAGE_BITS 12
#define TRUE 1
#define FALSE 0


/* frame_table protected by spinlock (interrupt disabling on
 * uniprocessor) as this implementation does not block.
 */ 

static struct spinlock frame_table_spinlock = SPINLOCK_INITIALIZER;

/*
 * Called very early in system boot to figure out how much physical
 * RAM is available.
 */
void
ram_bootstrap(void)
{
	size_t ramsize, frametable_size;
        uint32_t npages, i;

	/* Get size of RAM. */
	ramsize = mainbus_ramsize();

	/*
	 * This is the same as the last physical address, as long as
	 * we have less than 512 megabytes of memory. If we had more,
	 * we wouldn't be able to access it all through kseg0 and
	 * everything would get a lot more complicated. This is not a
	 * case we are going to worry about.
	 */
	if (ramsize > 512*1024*1024) {
		ramsize = 512*1024*1024;
	}

	lastpaddr = ramsize;

	/*
	 * Get first free virtual address from where start.S saved it.
	 * Convert to physical address.
	 */
	firstpaddr = firstfree - MIPS_KSEG0;

	kprintf("%uk physical memory available\n",
		(lastpaddr-firstpaddr)/1024);

        /*
         * Now do a little sanity checking of assumptions
         * the addresses should be page aligned at this point
         */

        KASSERT((firstpaddr & PAGE_FRAME) == firstpaddr);
	KASSERT((lastpaddr & PAGE_FRAME) == lastpaddr);

        npages = lastpaddr / PAGE_SIZE; /* number of pages in ram */
        last_frame = npages;

        frametable_size = npages * sizeof(ft_entry_t);
        frametable_size = ROUNDUP(frametable_size,PAGE_SIZE);

        /* grab pages for the frame table and bump the first free address */
        frame_table = (ft_entry_t *) PADDR_TO_KVADDR(firstpaddr);
        firstpaddr += frametable_size;

        if (firstpaddr >= lastpaddr) {
                /* This should never happen */
                panic("vm: frame table took up all of physical memory");
                
        }

        /* Now initialise the frame table in two ranges. */

        /* The first range of frames are used by the kernel already
         * and frametable itself, so mark as used.
         */

        for (i = 0; i < (firstpaddr >> PAGE_BITS); i++) {
                /* Mark as allocated as individual pages */
                frame_table[i].allocated = TRUE;
                frame_table[i].not_last = FALSE;
        }                                            
        
        /* 
         * The second range of frames are free
         */
        
        first_frame = firstpaddr >> PAGE_BITS;
        
        for (i = first_frame; i < (lastpaddr >> PAGE_BITS); i++) {
                frame_table[i].allocated = FALSE;
        }

        
}

/*
 * This function is intended to be called by the VM system when it
 * initializes in order to find out what memory it has available to
 * manage. Physical memory begins at physical address 0 and ends with
 * the address returned by this function. We assume that physical
 * memory is contiguous. This is not universally true, but is true on
 * the MIPS platforms we intend to run on.
 *
 * lastpaddr is constant once set by ram_bootstrap(), so this function
 * need not be synchronized.
 *
 * It is recommended, however, that this function be used only to
 * initialize the VM system, after which the VM system should take
 * charge of knowing what memory exists.
 */
paddr_t
ram_getsize(void)
{
	return lastpaddr;
}

/*
 * This function is intended to be called by the VM system when it
 * initializes in order to find out what memory it has available to
 * manage.
 *
 * It can only be called once, and once called ram_stealmem() will
 * no longer work, as that would invalidate the result it returned
 * and lead to multiple things using the same memory.
 *
 * This function should not be called once the VM system is initialized,
 * so it is not synchronized.
 */
paddr_t
ram_getfirstfree(void)
{
	paddr_t ret;

	ret = firstpaddr;
	firstpaddr = lastpaddr = 0;
	return ret;
}

/*
 * This is a relatively inefficient first-fit allocator. Single pages
 * always fit. Multiframe allocations can suffer from external
 * fragmentation. It is intended to be easy to understand and robust,
 * not efficient.
 */


static paddr_t alloc_one_frame(unsigned int npages)
{
        unsigned int i;

        /* 
         * Just scan from the start of the frame_table array for an
         * unallocated block
         */
        
        KASSERT(npages == 1);

        spinlock_acquire(&frame_table_spinlock);
        for (i =  first_frame; i < last_frame; i++) {
                if (frame_table[i].allocated == FALSE) {
                        frame_table[i].allocated = TRUE;
                        frame_table[i].not_last = FALSE;

                        spinlock_release(&frame_table_spinlock);

                        return (paddr_t) (i << PAGE_BITS);
                }
        }
        
        /* Did not find an unallocated frame :-( */

        spinlock_release(&frame_table_spinlock);
        return (paddr_t) 0;
}

static paddr_t alloc_multiple_frames(unsigned int npages)
{
        unsigned int i,j;


        /* scan from 'i' for the number of needed free frames. If an
         * allocated frame is encountered, restart the scan from after
         * that point.
         */
        

        spinlock_acquire(&frame_table_spinlock);

        i = first_frame; j = 0;

        while (i < (last_frame - npages) && j < npages) {
                if (frame_table[i+j].allocated == TRUE) {
                        i = i + j + 1; /* continue scan after allocated frame */
                        j = 0;         /* restart the count */
                }
                else {
                        j = j + 1; /* increment count of free frames */
                }
        }

        if  (j == npages) { /* we exited as we found the number of frames required. */
                for (j = i; j < i + npages - 1; j++) {
                        frame_table[j].allocated = TRUE; /* mark frame allocated */
                        frame_table[j].not_last = TRUE;  /* as a contiguous block */
                }
                frame_table[j].allocated = TRUE;
                frame_table[j].not_last = FALSE;

                spinlock_release(&frame_table_spinlock);
                
                return (paddr_t) (i << PAGE_BITS);
        }
        
        /* Did not find an unallocated contiguous range of frames :-( */

        spinlock_release(&frame_table_spinlock);
        return (paddr_t) 0;
}

static void free_frames(vaddr_t vaddr)
{
        paddr_t paddr;
        uint32_t i;

        KASSERT(vaddr != (vaddr_t) NULL);

        paddr = KVADDR_TO_PADDR(vaddr);

        i = paddr >> PAGE_BITS;

        spinlock_acquire(&frame_table_spinlock);

        if (frame_table[i].allocated == FALSE) { /* check for double free error */
                panic("Double free error!!");
        }
        
        while (frame_table[i].allocated == TRUE) { /* otherwise mark block free */
                frame_table[i].allocated = FALSE;
                if (frame_table[i].not_last == TRUE) {
                        i++;
                }
        }
        spinlock_release(&frame_table_spinlock);
}
        
/* Allocate/free some kernel-space virtual pages */
vaddr_t
alloc_kpages(unsigned npages)
{
        paddr_t paddr;
        if (npages > 1 ) {
                paddr = alloc_multiple_frames(npages);
        }
        else {
                paddr = alloc_one_frame(npages);
        }
        
	if (paddr == 0) {
		return 0;
	}
	return PADDR_TO_KVADDR(paddr);
}

void
free_kpages(vaddr_t addr)
{
        free_frames(addr);
}

