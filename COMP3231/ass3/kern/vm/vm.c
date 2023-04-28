#include <types.h>
#include <kern/errno.h>
#include <lib.h>
#include <thread.h>
#include <addrspace.h>
#include <vm.h>
#include <machine/tlb.h>
#include <proc.h>
#include <current.h>
#include <elf.h>
#include <addrspace.h>
#include <spl.h>

size_t hpt_size = 0;

/* Place your page table functions here */
void 
vm_bootstrap(void)
{
    /* Initialise any global components of your VM sub-system here.  
     *  
     * You may or may not need to add anything here depending what's
     * provided or required by the assignment spec.
     */
    hpt_size = (size_t)(ram_getsize() / PAGE_SIZE) * 2;
}

int 
vm_fault(int faulttype, vaddr_t faultaddress)
{
    // Check for invalid inputs or read-only faults
    if (curproc == NULL || faultaddress == 0 || faulttype == VM_FAULT_READONLY) return EFAULT;
    if (faulttype != VM_FAULT_READ && faulttype != VM_FAULT_WRITE) return EINVAL;
    
    // Align the fault address to a page boundary
    faultaddress &= PAGE_FRAME;

    // Get the current process address space
    struct addrspace *as = proc_getas();
    // Check if the address space and its components are valid
    if (as == NULL || as->as_hpt == NULL || as->as_region == NULL || as->as_lock == NULL) return EFAULT;

    // Acquire the address space lock
    lock_acquire(as->as_lock);

    // Find the corresponding region for the fault address
    struct region *r;
    for (r = as->as_region; r != NULL; r = r->next) 
        if (faultaddress >= r->region_vbase && faultaddress < r->region_vbase + r->region_size) break;

    // If no matching region is found, release the lock and return an error
    if (r == NULL) {
        lock_release(as->as_lock);
        return EFAULT;
    }

    // Find the page table entry for the fault address
    struct pte *fault_pte = hpt_find(as, faultaddress);

    // If the page table entry is not found, allocate a new page and insert it into the hash page table
    if (fault_pte == NULL) {
        vaddr_t vaddr = alloc_kpages(1);
        if (vaddr == 0) {
            lock_release(as->as_lock);
            return ENOMEM;
        }
        paddr_t paddr = KVADDR_TO_PADDR(vaddr);

        fault_pte = hpt_insert(as, faultaddress, paddr & TLBLO_PPAGE, r->writeable);
        if (fault_pte == NULL) {
            free_kpages(vaddr);
            lock_release(as->as_lock);
            return ENOMEM;
        }
    }

    // Update the TLB with the new entry
    int spl = splhigh();
    tlb_random(fault_pte->entryhi, fault_pte->entrylo);
    splx(spl);

    lock_release(as->as_lock);
    return 0;
}

/*
 * SMP-specific functions.  Unused in our UNSW configuration.
 */

void
vm_tlbshootdown(const struct tlbshootdown *ts)
{
	(void)ts;
	panic("vm tried to do tlb shootdown?!\n");
}

size_t 
hash_index(struct addrspace *as, vaddr_t faultaddr) {
    return ((uint32_t) as ^ (faultaddr >> 12)) % hpt_size;
}

int
hpt_init(struct addrspace *as) 
{
    // Check for invalid input
    if (as == NULL) return EINVAL;
    
    // Allocate memory for the hash page table with the specified size
    as->as_hpt = kmalloc(sizeof(struct pte) * hpt_size);
    
    // Initialize each entry in the hash page table
    for (size_t i = 0; i < hpt_size; ++i) {
        struct pte *temp = as->as_hpt + i;
        temp->as = NULL;
        temp->entryhi = 0;
        temp->entrylo = 0;
        temp->next = NULL;
    }

    // Check if the allocation was successful and return the appropriate result
    return as->as_hpt == NULL ? ENOMEM : 0;
}

struct pte * 
hpt_insert(struct addrspace *as, vaddr_t vaddr, paddr_t paddr, int dirty) 
{
    // Check for invalid input
    if (as == NULL || as->as_hpt == NULL || vaddr == 0 || paddr == 0) return NULL;

    // Set the Cache bit Valid bit and the Dirty bit if the page is writable
    paddr |= TLBLO_NOCACHE;
    if (dirty > 0) paddr |= TLBLO_DIRTY;
    paddr |= TLBLO_VALID;

    size_t index = hash_index(as, vaddr);
    
    // Iterate through the hash page table entries to find an empty slot
    struct pte *cur = as->as_hpt + index;
    for (size_t i = 0; i < hpt_size; ++i, cur = as->as_hpt + ((index + 1) % hpt_size)) {
        // If an empty slot is found, insert the new page table entry
        if (cur->as == NULL) {
            cur->as = as;
            cur->entryhi = vaddr;
            cur->entrylo = paddr;
            return cur;
        }
    }

    return NULL;
}   

int
hpt_copy(struct addrspace *old_as, struct addrspace *new_as) 
{
    // Check for invalid input
    if (old_as == NULL || old_as->as_hpt == NULL || new_as == NULL) return EINVAL;

    // Iterate through the hash page table entries
    for (size_t index = 0; index < hpt_size; index++) {
        struct pte *old_entry = old_as->as_hpt + index;

        // Check if the entry belongs to the old address space and is valid
        if (old_entry->as == old_as && (old_entry->entrylo & TLBLO_VALID) == TLBLO_VALID) {
            // Allocate a new physical page for the new address space
            vaddr_t vaddr = alloc_kpages(1);
            if (vaddr == 0) return ENOMEM;

            // Convert the allocated virtual address to a physical address，get the old physical address from the old 
            // entry and then copy the contents of the old page to the new page
            paddr_t paddr = KVADDR_TO_PADDR(vaddr);
            paddr_t old_paddr = old_entry->entrylo & TLBLO_PPAGE;
            memcpy((void *)PADDR_TO_KVADDR(paddr), (const void *)PADDR_TO_KVADDR(old_paddr), PAGE_SIZE);

            // Insert the new entry into the new address space's hash page table
            hpt_insert(new_as, old_entry->entryhi, paddr & TLBLO_PPAGE, (old_entry->entrylo & TLBLO_DIRTY) > 0 ? 1 : 0);
        }
    }

    return 0;
}

struct pte *
hpt_find(struct addrspace *as, vaddr_t vaddr) 
{
    // Check for invalid input
    if (as == NULL || as->as_hpt == NULL) return NULL;

    // Calculate the hash index for the given address space and virtual address
    size_t index = hash_index(as, vaddr);
    
    // Iterate through the hash page table entries to find the desired entry
    struct pte *cur = as->as_hpt + index;
    for (size_t i = 0; i < hpt_size; ++i, cur = as->as_hpt + ((index + 1) % hpt_size)) {
        // Check if the entry belongs to the given address space and has the desired virtual address
        if (cur->as == as && cur->entryhi == vaddr) {
            // Check the entry's validity
            uint32_t validity = cur->entrylo & TLBLO_VALID;
            // If the entry is valid, return it
            if (validity == TLBLO_VALID) return cur;
        }
    }

    return NULL;
}

void 
hpt_free(struct addrspace *as) 
{
    // Check for invalid input
    if (as == NULL) return;

    // Iterate through the hash page table entries
    for (size_t index = 0; index < hpt_size; index++) {
        struct pte *cur = as->as_hpt + index;

        // Check if the entry belongs to the given address space and is valid
        if (cur->as == as && (cur->entrylo & TLBLO_VALID) == TLBLO_VALID) {
            // Get the physical address from the entry and clear the cache, dirty, and valid bits，free the 
            // physical page associated with the entry
            paddr_t temp = cur->entrylo;
            temp &= ~TLBLO_NOCACHE;
            temp &= ~TLBLO_DIRTY;
            temp &= ~TLBLO_VALID;
            free_kpages(PADDR_TO_KVADDR(temp));
        }
    }

    // Free the memory allocated for the hash page table
    kfree(as->as_hpt);
}
