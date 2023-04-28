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

/*
 * Wait test code.
 */
#include <types.h>
#include <kern/wait.h>
#include <lib.h>
#include <stdarg.h>
#include <spl.h>
#include <thread.h>
#include <proc.h>
#include <current.h>
#include <synch.h>
#include <pid.h>
#include <test.h>
//#include <queue.h> // XXX

#define NTHREADS  8

static struct semaphore *exitsems[NTHREADS];

static
void
init_sem(void)
{
	int i;
	for (i = 0; i < NTHREADS; i++) {
		if (exitsems[i] == NULL) {
			exitsems[i] = sem_create("waitsem", 0);
			if (exitsems[i] == NULL) {
				panic("waittest: sem_create failed\n");
			}
		}
	}
}

static
void
waitfirstthread(void *junk, unsigned long num)
{
	unsigned long i;
	(void)junk;

	kprintf("waitfirstthread %lu started...\n", num);

	for (i = 0; i < 100 * (num + 1); i++)
		thread_yield();

	kprintf("waitfirstthread %lu exiting.\n", num);

	proc_exit(_MKWAIT_EXIT(num));
	thread_exit();
}

static
void
exitfirstthread(void *junk, unsigned long num)
{
	unsigned long i;
	(void)junk;

	kprintf("exitfirstthread %lu started...\n", num);

	for (i = 0; i <  100 * (num + 1); i++)
		thread_yield();

	kprintf("exitfirstthread %lu exiting.\n", num);

	V(exitsems[num]);

	proc_exit(_MKWAIT_EXIT(num));
	thread_exit();
}

static
int
dofork(const char *name, void (*func)(void *, unsigned long),
       void *ptrarg, unsigned long numarg, pid_t *ret_pid)
{
	struct proc *proc;
	int result;

	result = proc_fork(&proc);
	if (result) {
		return result;
	}
	*ret_pid = proc->p_pid;
	result = thread_fork(name, proc, func, ptrarg, numarg);
	if (result) {
		proc_unfork(proc);
		return result;
	}
	return 0;
}

static
void
printstatus(pid_t kid, int err, int status)
{
	if (err) {
		kprintf("Pid %d waitpid error %d!\n", kid, err);
	}
	else if (WIFEXITED(status)) {
		kprintf("Pid %d exit status: %d\n", kid, WEXITSTATUS(status));
	}
	else if (WIFSIGNALED(status)) {
		kprintf("Pid %d exit signal: %d\n", kid, WTERMSIG(status));
	}
	else {
		kprintf("Pid %d bad exit status %d\n", kid, status);
	}
}

int
waittest(int nargs, char **args)
{
	int i, spl, status, err;
	pid_t kid;

	pid_t kids2[NTHREADS];
	int kids2_head = 0, kids2_tail = 0;

	(void)nargs;
	(void)args;

	init_sem();

	kprintf("Starting wait test...\n");

	/*
	 * This first set should (hopefully) still be running when
	 * wait is called (helped by the splhigh).
	 */

	kprintf("\n");
	kprintf("Set 1 (wait should generally succeed)\n");
	kprintf("-------------------------------------\n");

	spl = splhigh();
	for (i = 0; i < NTHREADS; i++) {
		err = dofork("wait test thread", waitfirstthread, NULL, i,
			     &kid);
		if (err) {
			panic("waittest: dofork failed (%d)\n", err);
		}
		kprintf("Spawned pid %d\n", kid);
		kids2[kids2_tail] = kid;
		kids2_tail = (kids2_tail+1) % NTHREADS;
	}
	splx(spl);

	for (i = 0; i < NTHREADS; i++) {
		kid = kids2[kids2_head];
		kids2_head = (kids2_head+1) % NTHREADS;
		kprintf("Waiting on pid %d...\n", kid);
		err = pid_wait(kid, &status, 0, NULL);
		printstatus(kid, err, status);
	}

	/*
	 * This second set has to V their semaphore before the exit,
	 * so when wait is called, they will have already exited, but
	 * their parent is still alive.
	 */

	kprintf("\n");
	kprintf("Set 2 (wait should always succeed)\n");
	kprintf("----------------------------------\n");

	for (i = 0; i < NTHREADS; i++) {
		err = dofork("wait test thread", exitfirstthread, NULL, i,
			     &kid);
		if (err) {
			panic("waittest: dofork failed (%d)\n", err);
		}
		kprintf("Spawned pid %d\n", kid);
		kids2[kids2_tail] = kid;
		kids2_tail = (kids2_tail+1) % NTHREADS;
		if (err) {
			panic("waittest: q_addtail failed (%d)\n", err);
		}
	}

	for (i = 0; i < NTHREADS; i++) {
		kid = kids2[kids2_head];
		kids2_head = (kids2_head+1) % NTHREADS;
		kprintf("Waiting for pid %d to V()...\n", kid);
		P(exitsems[i]);
		kprintf("Appears that pid %d P()'d\n", kid);
		kprintf("Waiting on pid %d...\n", kid);
		err = pid_wait(kid, &status, 0, NULL);
		printstatus(kid, err, status);
	}

	/*
	 * This third set has to V their semaphore before the exit, so
	 * when wait is called, they will have already exited, and
	 * since we've gone through and disowned them all, their exit
	 * statuses should have been disposed of already and our waits
	 * should all fail.
	 */

	kprintf("\n");
	kprintf("Set 3 (wait should never succeed)\n");
	kprintf("---------------------------------\n");

	for (i = 0; i < NTHREADS; i++) {
		err = dofork("wait test thread", exitfirstthread, NULL, i,
				  &kid);
		if (err) {
			panic("waittest: dofork failed (%d)\n", err);
		}
		kprintf("Spawned pid %d\n", kid);

		pid_disown(kid);

		kids2[kids2_tail] = kid;
		kids2_tail = (kids2_tail+1) % NTHREADS;
	}

	for (i = 0; i < NTHREADS; i++) {
		kid = kids2[kids2_head];
		kids2_head = (kids2_head+1) % NTHREADS;
		kprintf("Waiting for pid %d to V()...\n", kid);
		P(exitsems[i]);
		kprintf("Appears that pid %d P()'d\n", kid);
		kprintf("Waiting on pid %d...\n", kid);
		err = pid_wait(kid, &status, 0, NULL);
		printstatus(kid, err, status);
	}

	kprintf("\nWait test done.\n");

	return 0;
}
