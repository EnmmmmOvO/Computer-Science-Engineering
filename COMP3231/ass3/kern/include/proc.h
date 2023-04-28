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

#ifndef _PROC_H_
#define _PROC_H_

/*
 * Definition of a process.
 *
 * Note: curproc is defined by <current.h>.
 */

#include <spinlock.h>
#include <thread.h> /* required for struct threadarray */

struct addrspace;
struct vnode;

/*
 * Process structure.
 *
 * Note that unless you implement multithreaded processes, p_threads
 * will only contain one thread for all processes other than kproc.
 *
 * Note: you can't protect p_threads with a spinlock because it needs
 * to be able to call kmalloc.
 */
struct proc {
	char *p_name;			/* Name of this process */
	struct lock *p_threadslock;	/* Lock for p_threads */
	struct threadarray p_threads;	/* Threads in this process */
	struct spinlock p_lock;		/* Lock for rest of this structure */
	pid_t p_pid;			/* Process ID */

	/* VM */
	struct addrspace *p_addrspace;	/* virtual address space */

	/* VFS */
	struct vnode *p_cwd;		/* current working directory */
	struct filetable *p_filetable;	/* table of open files */

	/* add more material here as needed */
};

/* This is the process structure for the kernel and for kernel-only threads. */
extern struct proc *kproc;

/* Call once during system startup to allocate data structures. */
void proc_bootstrap(void);

/* Create a fresh process for use by runprogram(). */
int proc_create_runprogram(const char *name, struct proc **ret);

/* Create a fresh process for use by fork() */
int proc_fork(struct proc **ret);

/* Undo proc_fork if nothing's run in the new process yet. */
void proc_unfork(struct proc *proc);

/* Destroy a process. */
void proc_destroy(struct proc *proc);

/*
 * Cause the current process to exit. The current thread switches
 * itself into the kernel process.
 *
 * The status code should be prepared with one of the _MKWAIT macros
 * defined in <kern/wait.h>.
 */
void proc_exit(int status);

/* Attach a thread to a process. Must not already have a process. */
int proc_addthread(struct proc *proc, struct thread *t);

/* Detach a thread from its process. */
void proc_remthread(struct thread *t);

/* Fetch the address space of the current process. */
struct addrspace *proc_getas(void);

/* Change the address space of the current process, and return the old one. */
struct addrspace *proc_setas(struct addrspace *);


#endif /* _PROC_H_ */
