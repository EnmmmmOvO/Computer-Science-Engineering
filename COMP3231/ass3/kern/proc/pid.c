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
 * Process ID management.
 */

#include <types.h>
#include <kern/errno.h>
#include <kern/wait.h>
#include <limits.h>
#include <lib.h>
#include <array.h>
#include <clock.h>
#include <thread.h>
#include <proc.h>
#include <current.h>
#include <synch.h>
#include <pid.h>

/*
 * Structure for holding exit data of a thread.
 *
 * If pi_ppid is INVALID_PID, the parent has gone away and will not be
 * waiting. If pi_ppid is INVALID_PID and pi_exited is true, the
 * structure can be freed.
 */
struct pidinfo {
	pid_t pi_pid;			// process id of this thread
	pid_t pi_ppid;			// process id of parent thread
	volatile bool pi_exited;	// true if thread has exited
	int pi_exitstatus;		// status (only valid if exited)
	struct cv *pi_cv;		// use to wait for thread exit
};


/*
 * Global pid and exit data.
 *
 * The process table is an el-cheapo hash table. It's indexed by
 * (pid % PROCS_MAX), and only allows one process per slot. If a
 * new pid allocation would cause a hash collision, we just don't
 * use that pid.
 */
static struct lock *pidlock;		// lock for global exit data
static struct pidinfo *pidinfo[PROCS_MAX]; // actual pid info
static pid_t nextpid;			// next candidate pid
static int nprocs;			// number of allocated pids



/*
 * Create a pidinfo structure for the specified pid.
 */
static
struct pidinfo *
pidinfo_create(pid_t pid, pid_t ppid)
{
	struct pidinfo *pi;

	KASSERT(pid != INVALID_PID);

	pi = kmalloc(sizeof(struct pidinfo));
	if (pi==NULL) {
		return NULL;
	}

	pi->pi_cv = cv_create("pidinfo cv");
	if (pi->pi_cv == NULL) {
		kfree(pi);
		return NULL;
	}

	pi->pi_pid = pid;
	pi->pi_ppid = ppid;
	pi->pi_exited = false;
	pi->pi_exitstatus = 0xbeef;  /* Recognizably invalid value */

	return pi;
}

/*
 * Clean up a pidinfo structure.
 */
static
void
pidinfo_destroy(struct pidinfo *pi)
{
	KASSERT(pi->pi_exited == true);
	KASSERT(pi->pi_ppid == INVALID_PID);
	cv_destroy(pi->pi_cv);
	kfree(pi);
}

////////////////////////////////////////////////////////////

/*
 * pid_bootstrap: initialize.
 */
void
pid_bootstrap(void)
{
	int i;

	pidlock = lock_create("pidlock");
	if (pidlock == NULL) {
		panic("Out of memory creating pid lock\n");
	}

	/* not really necessary - should start zeroed */
	for (i=0; i<PROCS_MAX; i++) {
		pidinfo[i] = NULL;
	}

	pidinfo[KERNEL_PID] = pidinfo_create(KERNEL_PID, INVALID_PID);
	if (pidinfo[KERNEL_PID]==NULL) {
		panic("Out of memory creating kernel pid data\n");
	}

	nextpid = PID_MIN;
	nprocs = 1;
}

/*
 * pi_get: look up a pidinfo in the process table.
 */
static
struct pidinfo *
pi_get(pid_t pid)
{
	struct pidinfo *pi;

	KASSERT(pid>=0);
	KASSERT(pid != INVALID_PID);
	KASSERT(lock_do_i_hold(pidlock));

	pi = pidinfo[pid % PROCS_MAX];
	if (pi==NULL) {
		return NULL;
	}
	if (pi->pi_pid != pid) {
		return NULL;
	}
	return pi;
}

/*
 * pi_put: insert a new pidinfo in the process table. The right slot
 * must be empty.
 */
static
void
pi_put(pid_t pid, struct pidinfo *pi)
{
	KASSERT(lock_do_i_hold(pidlock));

	KASSERT(pid != INVALID_PID);

	KASSERT(pidinfo[pid % PROCS_MAX] == NULL);
	pidinfo[pid % PROCS_MAX] = pi;
	nprocs++;
}

/*
 * pi_drop: remove a pidinfo structure from the process table and free
 * it. It should reflect a process that has already exited and been
 * waited for.
 */
static
void
pi_drop(pid_t pid)
{
	struct pidinfo *pi;

	KASSERT(lock_do_i_hold(pidlock));

	pi = pidinfo[pid % PROCS_MAX];
	KASSERT(pi != NULL);
	KASSERT(pi->pi_pid == pid);

	pidinfo_destroy(pi);
	pidinfo[pid % PROCS_MAX] = NULL;
	nprocs--;
}

////////////////////////////////////////////////////////////

/*
 * Helper function for pid_alloc.
 */
static
void
inc_nextpid(void)
{
	KASSERT(lock_do_i_hold(pidlock));

	nextpid++;
	if (nextpid > PID_MAX) {
		nextpid = PID_MIN;
	}
}

/*
 * pid_alloc: allocate a process id.
 */
int
pid_alloc(pid_t *retval)
{
	struct pidinfo *pi;
	pid_t pid;
	int count;

	KASSERT(curproc->p_pid != INVALID_PID);

	/* lock the table */
	lock_acquire(pidlock);

	if (nprocs == PROCS_MAX) {
		lock_release(pidlock);
		return EAGAIN;
	}

	/*
	 * The above test guarantees that this loop terminates, unless
	 * our nprocs count is off. Even so, assert we aren't looping
	 * forever.
	 */
	count = 0;
	while (pidinfo[nextpid % PROCS_MAX] != NULL) {

		/* avoid various boundary cases by allowing extra loops */
		KASSERT(count < PROCS_MAX*2+5);
		count++;

		inc_nextpid();
	}

	pid = nextpid;

	pi = pidinfo_create(pid, curproc->p_pid);
	if (pi==NULL) {
		lock_release(pidlock);
		return ENOMEM;
	}

	pi_put(pid, pi);

	inc_nextpid();

	lock_release(pidlock);

	*retval = pid;
	return 0;
}

/*
 * pid_unalloc - unallocate a process id (allocated with pid_alloc) that
 * hasn't run yet.
 */
void
pid_unalloc(pid_t theirpid)
{
	struct pidinfo *them;

	KASSERT(theirpid >= PID_MIN && theirpid <= PID_MAX);

	lock_acquire(pidlock);

	them = pi_get(theirpid);
	KASSERT(them != NULL);
	KASSERT(them->pi_exited == false);
	KASSERT(them->pi_ppid == curproc->p_pid);

	/* keep pidinfo_destroy from complaining */
	them->pi_exitstatus = 0xdead;
	them->pi_exited = true;
	them->pi_ppid = INVALID_PID;

	pi_drop(theirpid);

	lock_release(pidlock);
}

/*
 * pid_disown - disown any interest in waiting for a child's exit
 * status.
 */
void
pid_disown(pid_t theirpid)
{
	struct pidinfo *them;

	KASSERT(theirpid >= PID_MIN && theirpid <= PID_MAX);

	lock_acquire(pidlock);

	them = pi_get(theirpid);
	KASSERT(them != NULL);
	KASSERT(them->pi_ppid==curproc->p_pid);

	them->pi_ppid = INVALID_PID;
	if (them->pi_exited) {
		pi_drop(them->pi_pid);
	}

	lock_release(pidlock);
}

/*
 * pid_setexitstatus: Sets the exit status of this process. Must only
 * be called if the thread actually had a pid assigned. Wakes up any
 * waiters and disposes of the piddata if nobody else is still using it.
 *
 * As far as the process is concerned, this releases its pid for
 * subsequent reuse; thus we set curproc->p_pid to INVALID_PID.
 */
void
pid_setexitstatus(int status)
{
	struct pidinfo *us;
	int i;

	lock_acquire(pidlock);
	KASSERT(curproc->p_pid != INVALID_PID);

	/* First, disown all children */
	for (i=0; i<PROCS_MAX; i++) {
		if (pidinfo[i]==NULL) {
			continue;
		}
		if (pidinfo[i]->pi_ppid == curproc->p_pid) {
			pidinfo[i]->pi_ppid = INVALID_PID;
			if (pidinfo[i]->pi_exited) {
				pi_drop(pidinfo[i]->pi_pid);
			}
		}
	}

	/* Now, wake up our parent */
	us = pi_get(curproc->p_pid);
	KASSERT(us != NULL);

	us->pi_exitstatus = status;
	us->pi_exited = true;

	if (us->pi_ppid == INVALID_PID) {
		/* no parent */
		pi_drop(curproc->p_pid);
	}
	else {
		cv_broadcast(us->pi_cv, pidlock);
	}

	curproc->p_pid = INVALID_PID;
	lock_release(pidlock);
}

/*
 * Waits on a pid, returning the exit status when it's available.
 * status and ret are a kernel pointers, but pid/flags may come from
 * userland and may thus be maliciously invalid.
 *
 * status may be null, in which case the status is thrown away. ret
 * may only be null if WNOHANG is not set.
 */
int
pid_wait(pid_t theirpid, int *status, int flags, pid_t *ret)
{
	struct pidinfo *them;

	KASSERT(curproc->p_pid != INVALID_PID);

	/* Don't let a process wait for itself. */
	if (theirpid == curproc->p_pid) {
		return EINVAL;
	}

	/*
	 * We don't support the Unix meanings of negative pids or 0
	 * (0 is INVALID_PID) and other code may break on them, so
	 * check now.
	 */
	if (theirpid == INVALID_PID || theirpid<0) {
		return ENOSYS;
	}

	/* Only valid options */
	if (flags != 0 && flags != WNOHANG) {
		return EINVAL;
	}

	lock_acquire(pidlock);

	them = pi_get(theirpid);
	if (them==NULL) {
		lock_release(pidlock);
		return ESRCH;
	}

	KASSERT(them->pi_pid==theirpid);

	/* Only allow waiting for own children. */
	if (them->pi_ppid != curproc->p_pid) {
		lock_release(pidlock);
		return EPERM;
	}

	if (them->pi_exited == false) {
		if (flags == WNOHANG) {
			lock_release(pidlock);
			KASSERT(ret != NULL);
			*ret = 0;
			return 0;
		}
		/* don't need to loop on this */
		cv_wait(them->pi_cv, pidlock);
		KASSERT(them->pi_exited == true);
	}

	if (status != NULL) {
		*status = them->pi_exitstatus;
	}
	if (ret != NULL) {
		/*
		 * In Unix you can wait for any of several possible
		 * processes by passing particular magic values of
		 * pid. wait then returns the pid you actually
		 * found. We don't support this, so always return the
		 * pid we looked for.
		 */
		*ret = theirpid;
	}

	them->pi_ppid = 0;
	pi_drop(them->pi_pid);

	lock_release(pidlock);
	return 0;
}
