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
#include <kern/errno.h>
#include <lib.h>
#include <spl.h>
#include <spinlock.h>
#include <current.h>
#include <mips/tlb.h>
#include <addrspace.h>
#include <vm.h>
#include <proc.h>
#include <elf.h>

/*
 * Note! If OPT_DUMBVM is set, as is the case until you start the VM
 * assignment, this file is not compiled or linked or in any way
 * used. The cheesy hack versions in dumbvm.c are used instead.
 *
 * UNSW: If you use ASST3 config as required, then this file forms
 * part of the VM subsystem.
 *
 */

struct addrspace *
as_create(void)
{
	// Allocate memory for a new address space structure
    struct addrspace *as = kmalloc(sizeof(struct addrspace));
    if (as == NULL) return NULL;

    // Initialize the hash page table for the new address space
    int fault = hpt_init(as);
    if (fault != 0) {
        // If there is an error, free the memory and return NULL
        if (fault != EINVAL) kfree(as);
        return NULL;
    }
    
    // Initialize the regions list
    as->as_region = NULL;

    // Create a lock for the address space
    as->as_lock = lock_create("as_lock");
    if (as->as_lock == NULL) {
        // If lock creation fails, free the hash page table, free the address space, and return NULL
        hpt_free(as);
        kfree(as);
        return NULL;
    }
    return as;
}

int 
as_copy(struct addrspace *old_as, struct addrspace **ret) 
{ 
    // Check for invalid input
    if (old_as == NULL) return EINVAL;

    // Create a new address space
    struct addrspace *new_as = as_create();
    if (new_as == NULL) return ENOMEM;

    // Acquire lock on the old address space
    lock_acquire(old_as->as_lock);

    // Copy regions from the old address space to the new address space
    struct region *prev = NULL;
    for (struct region *old = old_as->as_region; old != NULL; old = old->next) {
        // Allocate memory for a new region and check for errors
        struct region *new_region = kmalloc(sizeof(struct region));
        if (new_region == NULL) {
            lock_release(old_as->as_lock);
            as_destroy(new_as);
            return ENOMEM;
        }

        // Copy region attributes from the old region to the new region
        new_region->region_vbase = old->region_vbase;
        new_region->region_size = old->region_size;
        new_region->readable = old->readable;
        new_region->writeable = old->writeable;
        new_region->executable = old->executable;
        new_region->checkable = old->checkable;
        new_region->next = NULL;

        // Link the new region to the new address space's region list
        if (new_as->as_region == NULL) new_as->as_region = new_region;
        else prev->next = new_region;
        prev = new_region;
    }

    // Copy the hash page table from the old address space to the new address space
    if (hpt_copy(old_as, new_as) != 0) {
        lock_release(old_as->as_lock);
        as_destroy(new_as);
        return ENOMEM;
    }

    // Set the return value and release the lock
    *ret = new_as;
    lock_release(old_as->as_lock);
    return 0;
}

void
as_destroy(struct addrspace *as)
{
    // Check for invalid input
    if (as == NULL) return;

    // Acquire lock on the address space
    lock_acquire(as->as_lock);

    // Free regions in the address space
    struct region *free_node = as->as_region;
    struct region *temp;

    while (free_node != NULL) {
        temp = free_node;
        free_node = free_node->next;
        kfree(temp);
    }

    // Free the hash page table
    hpt_free(as);

    // Release the lock and destroy it
    lock_release(as->as_lock);
    lock_destroy(as->as_lock);

    // Free the address space
    kfree(as);
}

void
as_activate(void)
{
    // Copy from dumbvm.c
	int i, spl;
	struct addrspace *as;

	as = proc_getas();
	if (as == NULL) {
		return;
	}

	/* Disable interrupts on this CPU while frobbing the TLB. */
	spl = splhigh();

	for (i=0; i<NUM_TLB; i++) {
		tlb_write(TLBHI_INVALID(i), TLBLO_INVALID(), i);
	}

	splx(spl);
}

void
as_deactivate(void)
{
	/*
	 * Write this. For many designs it won't need to actually do
	 * anything. See proc.c for an explanation of why it (might)
	 * be needed.
	 */
    as_activate();
}

/*
 * Set up a segment at virtual address VADDR of size MEMSIZE. The
 * segment in memory extends from VADDR up to (but not including)
 * VADDR+MEMSIZE.
 *
 * The READABLE, WRITEABLE, and EXECUTABLE flags are set if read,
 * write, or execute permission should be set on the segment. At the
 * moment, these are ignored. When you write the VM system, you may
 * want to implement them.
 */

int
as_define_region(struct addrspace *as, vaddr_t vaddr, size_t memsize,
		 int readable, int writeable, int executable)
{
    // Check for invalid input
    if (as == NULL && (memsize == 0 || memsize > MIPS_KSEG0 - MIPS_KSEG1)) return EINVAL;

    // Acquire lock on the address space
    lock_acquire(as->as_lock);

    // Allocate memory for a new region
    struct region *new_region = kmalloc(sizeof(struct region));
  
    // Align vaddr and memsize to page boundaries
    memsize += vaddr & ~(vaddr_t)PAGE_FRAME;
    vaddr &= PAGE_FRAME;
    memsize = (memsize + PAGE_SIZE - 1) & PAGE_FRAME;
    
    // Set new region attributes
    new_region->region_vbase = vaddr;
    new_region->region_size = memsize;
    new_region->readable = readable;
    new_region->writeable = writeable;
    new_region->executable = executable;
    new_region->next = NULL;

    // Add the new region to the address space's region list
    if (as->as_region == NULL) as->as_region = new_region;
    else {
        struct region *r;
        for (r = as->as_region; r->next != NULL; r = r->next);
        r->next = new_region;
    }
    
    // Release the lock on the address space
    lock_release(as->as_lock);
    return 0;
}

int
as_prepare_load(struct addrspace *as)
{
    // Check for invalid input
    if (as == NULL) return EINVAL;
    
    // Acquire lock on the address space
    lock_acquire(as->as_lock);

    // Set regions to writeable and checkable
    for (struct region *r = as->as_region; r != NULL; r = r->next) {
        if (r->writeable == 0) {
            r->writeable = 1;
            r->checkable = 1;
        }
    }

    // Release the lock on the address space
    lock_release(as->as_lock);
    return 0;
}

int
as_complete_load(struct addrspace *as)
{
    // Check for invalid input
    if (as == NULL) return EINVAL;
        
    // Acquire lock on the address space
    lock_acquire(as->as_lock);

    // Set writeable regions back to read-only if they were checkable
    for (struct region *r = as->as_region; r != NULL; r = r->next) {
        if (r->checkable == 1) {
            r->writeable = 0;
            r->checkable = 0;
        }
    }

    // Release the lock on the address space
    lock_release(as->as_lock);
    return 0;
}

int
as_define_stack(struct addrspace *as, vaddr_t *stackptr)
{
    // Check for invalid input
    if (as == NULL) return EINVAL;
    
    // Set the stack pointer to the user stack
    *stackptr = USERSTACK;

    // Define the stack region in the address space
    if (as_define_region(as, USERSTACK - 16 * PAGE_SIZE, 16 * PAGE_SIZE, 1, 1, 1) == 0) return 0;
    else return EFAULT;
}

