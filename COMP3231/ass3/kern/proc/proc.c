/*
 * Copyright (c) 2013
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

/*
 * Process support.
 *
 * There is (intentionally) not much here; you will need to add stuff
 * and maybe change around what's already present.
 *
 * p_lock is intended to be held when manipulating the pointers in the
 * proc structure, not while doing any significant work with the
 * things they point to. Rearrange this (and/or change it to be a
 * regular lock) as needed.
 *
 * Unless you're implementing multithreaded user processes, the only
 * process that will have more than one thread is the kernel process.
 */

#include <types.h>
#include <kern/errno.h>
#include <spl.h>
#include <synch.h>
#include <proc.h>
#include <current.h>
#include <addrspace.h>
#include <vnode.h>
#include <pid.h>
#include <filetable.h>

/*
 * The process for the kernel; this holds all the kernel-only threads.
 */
struct proc *kproc;

/*
 * Create a proc structure.
 */
static
struct proc *
proc_create(const char *name)
{
	struct proc *proc;

	proc = kmalloc(sizeof(*proc));
	if (proc == NULL) {
		return NULL;
	}
	proc->p_name = kstrdup(name);
	if (proc->p_name == NULL) {
		kfree(proc);
		return NULL;
	}

	proc->p_threadslock = lock_create("p_threads");
	if (proc->p_threadslock == NULL) {
		kfree(proc->p_name);
		kfree(proc);
		return NULL;
	}
	threadarray_init(&proc->p_threads);

	spinlock_init(&proc->p_lock);
	proc->p_pid = INVALID_PID;

	/* VM fields */
	proc->p_addrspace = NULL;

	/* VFS fields */
	proc->p_cwd = NULL;
	proc->p_filetable = NULL;

	return proc;
}

/*
 * Destroy a proc structure.
 *
 * Note: nothing currently calls this. Your wait/exit code will
 * probably want to do so.
 */
void
proc_destroy(struct proc *proc)
{
	/*
	 * You probably want to destroy and null out much of the
	 * process (particularly the address space) at exit time if
	 * your wait/exit design calls for the process structure to
	 * hang around beyond process exit. Some wait/exit designs
	 * do, some don't.
	 */

	KASSERT(proc != NULL);
	KASSERT(proc != kproc);

	/*
	 * We don't take p_lock in here because we must have the only
	 * reference to this structure. (Otherwise it would be
	 * incorrect to destroy it.)
	 */

	/* VFS fields */
	if (proc->p_cwd) {
		VOP_DECREF(proc->p_cwd);
		proc->p_cwd = NULL;
	}
	if (proc->p_filetable) {
		filetable_destroy(proc->p_filetable);
		proc->p_filetable = NULL;
	}

	/* VM fields */
	if (proc->p_addrspace) {
		/*
		 * If p is the current process, remove it safely from
		 * p_addrspace before destroying it. This makes sure
		 * we don't try to activate the address space while
		 * it's being destroyed.
		 *
		 * Also explicitly deactivate, because setting the
		 * address space to NULL won't necessarily do that.
		 *
		 * (When the address space is NULL, it means the
		 * process is kernel-only; in that case it is normally
		 * ok if the MMU and MMU- related data structures
		 * still refer to the address space of the last
		 * process that had one. Then you save work if that
		 * process is the next one to run, which isn't
		 * uncommon. However, here we're going to destroy the
		 * address space, so we need to make sure that nothing
		 * in the VM system still refers to it.)
		 *
		 * The call to as_deactivate() must come after we
		 * clear the address space, or a timer interrupt might
		 * reactivate the old address space again behind our
		 * back.
		 *
		 * If p is not the current process, still remove it
		 * from p_addrspace before destroying it as a
		 * precaution. Note that if p is not the current
		 * process, in order to be here p must either have
		 * never run (e.g. cleaning up after fork failed) or
		 * have finished running and exited. It is quite
		 * incorrect to destroy the proc structure of some
		 * random other process while it's still running...
		 */
		struct addrspace *as;

		if (proc == curproc) {
			as = proc_setas(NULL);
			as_deactivate();
		}
		else {
			as = proc->p_addrspace;
			proc->p_addrspace = NULL;
		}
		as_destroy(as);
	}

	KASSERT(proc->p_pid == INVALID_PID);
	spinlock_cleanup(&proc->p_lock);
	threadarray_cleanup(&proc->p_threads);
	lock_destroy(proc->p_threadslock);

	kfree(proc->p_name);
	kfree(proc);
}

/*
 * Create the process structure for the kernel.
 */
void
proc_bootstrap(void)
{
	kproc = proc_create("[kernel]");
	if (kproc == NULL) {
		panic("proc_create for kproc failed\n");
	}
	kproc->p_pid = KERNEL_PID;
}

/*
 * Create a fresh proc for use by runprogram.
 *
 * It will have no address space and will inherit the current
 * process's (that is, the kernel menu's) current directory.
 *
 * It will be given no filetable. The filetable will be initialized in
 * runprogram().
 */
int
proc_create_runprogram(const char *name, struct proc **ret)
{
	struct proc *newproc;
	int result;

	newproc = proc_create(name);
	if (newproc == NULL) {
		return ENOMEM;
	}
	/* Get a process ID */
	result = pid_alloc(&newproc->p_pid);
	if (result) {
		proc_destroy(newproc);
		return result;
	}

	/* VM fields */

	newproc->p_addrspace = NULL;

	/* VFS fields */

	/*
	 * Lock the current process to copy its current directory.
	 * (We don't need to lock the new process, though, as we have
	 * the only reference to it.)
	 */
	spinlock_acquire(&curproc->p_lock);
	if (curproc->p_cwd != NULL) {
		VOP_INCREF(curproc->p_cwd);
		newproc->p_cwd = curproc->p_cwd;
	}
	spinlock_release(&curproc->p_lock);

	*ret = newproc;
	return 0;
}

/*
 * Clone the current process.
 *
 * The new thread is given a copy of the caller's file handles if RET
 * is not null. (If RET is null, what we're creating is a kernel-only
 * thread and it doesn't need an address space or file handles.)
 * However, the new thread always inherits its current working
 * directory from the caller. The new thread is given no address space
 * (the caller decides that).
 */
int
proc_fork(struct proc **ret)
{
	struct proc *newproc;
	struct addrspace *as;
	struct filetable *tbl;
	int result;

	newproc = proc_create(curproc->p_name);
	if (newproc == NULL) {
		return ENOMEM;
	}
	/* Get a process ID */
	result = pid_alloc(&newproc->p_pid);
	if (result) {
		proc_destroy(newproc);
		return result;
	}

#if 0 /* not yet */
	/*
	 * If the caller doesn't want to collect the exit status,
	 * detach the new thread with pid_disown.
	 */
	if (...) {
		pid_disown(newproc->p_pid);
	}
#endif

	/* VM fields */
	as = proc_getas();
	if (as != NULL) {
		result = as_copy(as, &newproc->p_addrspace);
		if (result) {
			pid_unalloc(newproc->p_pid);
			newproc->p_pid = INVALID_PID;
			proc_destroy(newproc);
			return result;
		}
	}

	/* VFS fields */
	tbl = curproc->p_filetable;
	if (tbl != NULL) {
		result = filetable_copy(tbl, &newproc->p_filetable);
		if (result) {
			as_destroy(newproc->p_addrspace);
			newproc->p_addrspace = NULL;
			pid_unalloc(newproc->p_pid);
			newproc->p_pid = INVALID_PID;
			proc_destroy(newproc);
			return result;
		}
	}

	/*
	 * Lock the current process to copy its current directory.
	 * (We don't need to lock the new process, though, as we have
	 * the only reference to it.)
	 */
	spinlock_acquire(&curproc->p_lock);
	if (curproc->p_cwd != NULL) {
		VOP_INCREF(curproc->p_cwd);
		newproc->p_cwd = curproc->p_cwd;
	}
	spinlock_release(&curproc->p_lock);

	*ret = newproc;
	return 0;
}

/*
 * Undo proc_fork if nothing's run in the new process yet.
 */
void
proc_unfork(struct proc *newproc)
{
	pid_unalloc(newproc->p_pid);
	newproc->p_pid = INVALID_PID;
	proc_destroy(newproc);
}

/*
 * Make the current process exit.
 */
void
proc_exit(int status)
{
	struct proc *proc = curproc;

	/* The kernel isn't supposed to exit. */
	KASSERT(proc != kproc);

	/* Set exit status and wake up anyone waiting for us. */
	pid_setexitstatus(status);

	/* Detach from the process and attach to the kernel process. */
	KASSERT(curthread->t_proc == proc);
	proc_remthread(curthread);
	proc_addthread(kproc, curthread);

	/* There should be no threads left in the target process. */
	KASSERT(threadarray_num(&proc->p_threads) == 0);

	/* Now we can destroy the process. */
	proc_destroy(proc);

	thread_exit();
}

/*
 * Add a thread to a process. Either the thread or the process might
 * or might not be current.
 *
 * Turn off interrupts on the local cpu while changing t_proc, in
 * case it's current, to protect against the as_activate call in
 * the timer interrupt context switch, and any other implicit uses
 * of "curproc".
 */
int
proc_addthread(struct proc *proc, struct thread *t)
{
	int spl;
	int result;

	KASSERT(t->t_proc == NULL);

	lock_acquire(proc->p_threadslock);
	result = threadarray_add(&proc->p_threads, t, NULL);
	lock_release(proc->p_threadslock);
	if (result) {
		return result;
	}

	spl = splhigh();
	t->t_proc = proc;
	splx(spl);

	return 0;
}

/*
 * Remove a thread from its process. Either the thread or the process
 * might or might not be current.
 *
 * Turn off interrupts on the local cpu while changing t_proc, in
 * case it's current, to protect against the as_activate call in
 * the timer interrupt context switch, and any other implicit uses
 * of "curproc".
 */
void
proc_remthread(struct thread *t)
{
	struct proc *proc;
	unsigned num, i;
	int spl;

	proc = t->t_proc;
	KASSERT(proc != NULL);

	lock_acquire(proc->p_threadslock);
	/* ugh: find the thread in the array */
	num = threadarray_num(&proc->p_threads);
	for (i=0; i<num; i++) {
		if (threadarray_get(&proc->p_threads, i) == t) {
			threadarray_remove(&proc->p_threads, i);
			lock_release(proc->p_threadslock);
			goto finish;
		}
	}
	/* Did not find it. */
	lock_release(proc->p_threadslock);
	panic("Thread (%p) has escaped from its process (%p)\n", t, proc);

finish:
	spl = splhigh();
	t->t_proc = NULL;
	splx(spl);
}

/*
 * Fetch the address space of (the current) process.
 *
 * Caution: address spaces aren't refcounted. If you implement
 * multithreaded processes, make sure to set up a refcount scheme or
 * some other method to make this safe. Otherwise the returned address
 * space might disappear under you.
 */
struct addrspace *
proc_getas(void)
{
	struct addrspace *as;
	struct proc *proc = curproc;

	if (proc == NULL) {
		return NULL;
	}

	spinlock_acquire(&proc->p_lock);
	as = proc->p_addrspace;
	spinlock_release(&proc->p_lock);
	return as;
}

/*
 * Change the address space of (the current) process. Return the old
 * one for later restoration or disposal.
 */
struct addrspace *
proc_setas(struct addrspace *newas)
{
	struct addrspace *oldas;
	struct proc *proc = curproc;

	KASSERT(proc != NULL);

	spinlock_acquire(&proc->p_lock);
	oldas = proc->p_addrspace;
	proc->p_addrspace = newas;
	spinlock_release(&proc->p_lock);
	return oldas;
}
