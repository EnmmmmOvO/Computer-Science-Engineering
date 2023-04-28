/*
 * Copyright (c) 2000, 2001, 2002, 2003, 2004, 2005, 2008, 2009, 2014
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
 * Code for running a user program from the menu, and code for execv,
 * which have a lot in common.
 */

#include <types.h>
#include <kern/errno.h>
#include <kern/fcntl.h>
#include <kern/unistd.h>
#include <limits.h>
#include <lib.h>
#include <proc.h>
#include <current.h>
#include <synch.h>
#include <copyinout.h>
#include <addrspace.h>
#include <vm.h>
#include <vfs.h>
#include <openfile.h>
#include <filetable.h>
#include <syscall.h>
#include <test.h>

/*
 * argv buffer.
 *
 * This is an abstraction that holds an argv while it's being shuffled
 * through the kernel during exec.
 */
struct argbuf {
	char *data;
	size_t len;
	size_t max;
	int nargs;
	bool tooksem;
};

/*
 * Throttle to limit the number of processes in exec at once. Or,
 * rather, the number trying to use large exec buffers at once. See
 * design notes for the rationale.
 */
#define EXEC_BIGBUF_THROTTLE	1
static struct semaphore *execthrottle;

/*
 * Set things up.
 */
void
exec_bootstrap(void)
{
	execthrottle = sem_create("exec", EXEC_BIGBUF_THROTTLE);
	if (execthrottle == NULL) {
		panic("Cannot create exec throttle semaphore\n");
	}
}

/*
 * Initialize an argv buffer.
 */
static
void
argbuf_init(struct argbuf *buf)
{
	buf->data = NULL;
	buf->len = 0;
	buf->max = 0;
	buf->nargs = 0;
	buf->tooksem = false;
}

/*
 * Clean up an argv buffer when done.
 */
static
void
argbuf_cleanup(struct argbuf *buf)
{
	if (buf->data != NULL) {
		kfree(buf->data);
		buf->data = NULL;
	}
	buf->len = 0;
	buf->max = 0;
	buf->nargs = 0;
	if (buf->tooksem) {
		V(execthrottle);
		buf->tooksem = false;
	}
}

/*
 * Allocate the memory for an argv buffer.
 */
static
int
argbuf_allocate(struct argbuf *buf, size_t size)
{
	buf->data = kmalloc(size);
	if (buf->data == NULL) {
		return ENOMEM;
	}
	buf->max = size;
	return 0;
}

/*
 * Prepare an argv buffer for runprogram, using a kernel pointer.
 *
 * This only accepts a program name (not arbitrary arguments) from the
 * menu, but could easily be extended to support arbitrary arguments.
 */
static
int
argbuf_fromkernel(struct argbuf *buf, const char *progname)
{
	size_t len;
	int result;

	len = strlen(progname) + 1;

	result = argbuf_allocate(buf, len);
	if (result) {
		return result;
	}
	strcpy(buf->data, progname);
	buf->len = len;
	buf->nargs = 1;

	return 0;
}

/*
 * Copy an argv array into kernel space, using an argvdata buffer.
 */
static
int
argbuf_copyin(struct argbuf *buf, userptr_t uargv)
{
	userptr_t thisarg;
	size_t thisarglen;
	int result;

	/* loop through the argv, grabbing each arg string */
	buf->nargs = 0;
	while (1) {
		/*
		 * First, grab the pointer at argv.
		 * (argv is incremented at the end of the loop)
		 */
		result = copyin(uargv, &thisarg, sizeof(userptr_t));
		if (result) {
			return result;
		}

		/* If we got NULL, we're at the end of the argv. */
		if (thisarg == NULL) {
			break;
		}

		/* Use the pointer to fetch the argument string. */
		result = copyinstr(thisarg, buf->data + buf->len,
				   buf->max - buf->len, &thisarglen);
		if (result == ENAMETOOLONG) {
			return E2BIG;
		}
		else if (result) {
			return result;
		}

		/* Move ahead. Note: thisarglen includes the \0. */
		buf->len += thisarglen;
		uargv += sizeof(userptr_t);
		buf->nargs++;
	}

	return 0;
}

/*
 * Get an argv from user space.
 */
static
int
argbuf_fromuser(struct argbuf *buf, userptr_t uargv)
{
	int result;

	/* try with a small buffer */
	result = argbuf_allocate(buf, PAGE_SIZE);
	if (result) {
		return result;
	}

	/* do the copyin */
	result = argbuf_copyin(buf, uargv);
	if (result == E2BIG) {
		/*
		 * Try again with the full-size buffer. Just start
		 * over instead of trying to keep the page we already
		 * did; this is a bit inefficient but it's not that
		 * important.
		 */
		argbuf_cleanup(buf);
		argbuf_init(buf);

		/* Wait on the semaphore, to throttle this allocation */
		P(execthrottle);
		buf->tooksem = true;

		result = argbuf_allocate(buf, ARG_MAX);
		if (result) {
			return result;
		}

		result = argbuf_copyin(buf, uargv);
	}
	return result;
}

/*
 * Copy an argv out of kernel space to user space.
 *
 * Note: ustackp is an in/out argument.
 */
static
int
argbuf_copyout(struct argbuf *buf, vaddr_t *ustackp,
	       int *argc_ret, userptr_t *uargv_ret)
{
	vaddr_t ustack;
	userptr_t ustringbase, uargvbase, uargv_i;
	userptr_t thisarg;
	size_t thisarglen;
	size_t pos;
	int result;

	/* Begin the stack at the passed in top. */
	ustack = *ustackp;

	/*
	 * Allocate space.
	 *
	 * buf->pos is the amount of space used by the strings; put that
	 * first, then align the stack, then make space for the argv
	 * pointers. Allow an extra slot for the ending NULL.
	 */

	ustack -= buf->len;
	ustack -= (ustack & (sizeof(void *) - 1));
	ustringbase = (userptr_t)ustack;

	ustack -= (buf->nargs + 1) * sizeof(userptr_t);
	uargvbase = (userptr_t)ustack;

	/* Now copy the data out. */
	pos = 0;
	uargv_i = uargvbase;
	while (pos < buf->len) {
		/* The user address of the string will be ustringbase + pos. */
		thisarg = ustringbase + pos;

		/* Place it in the argv array. */
		result = copyout(&thisarg, uargv_i, sizeof(thisarg));
		if (result) {
			return result;
		}

		/* Push out the string. */
		result = copyoutstr(buf->data + pos, thisarg,
				    buf->len - pos, &thisarglen);
		if (result) {
			return result;
		}

		/* thisarglen includes the \0 */
		pos += thisarglen;
		uargv_i += sizeof(thisarg);
	}
	/* Should have come out even... */
	KASSERT(pos == buf->len);

	/* Add the NULL. */
	thisarg = NULL;
	result = copyout(&thisarg, uargv_i, sizeof(userptr_t));
	if (result) {
		return result;
	}

	*ustackp = ustack;
	*argc_ret = buf->nargs;
	*uargv_ret = uargvbase;
	return 0;
}

/*
 * Common code for execv and runprogram: loading the executable.
 */
static
int
loadexec(char *path, vaddr_t *entrypoint, vaddr_t *stackptr)
{
	struct addrspace *newvm, *oldvm;
	struct vnode *v;
	char *newname;
	int result;

	/* new name for thread */
	newname = kstrdup(path);
	if (newname == NULL) {
		return ENOMEM;
	}

	/* open the file. */
	result = vfs_open(path, O_RDONLY, 0, &v);
	if (result) {
		kfree(newname);
		return result;
	}

	/* make a new address space. */
	newvm = as_create();
	if (newvm == NULL) {
		vfs_close(v);
		kfree(newname);
		return ENOMEM;
	}

	/* replace address spaces, and activate the new one */
	oldvm = proc_setas(newvm);
	as_activate();

 	/*
	 * Load the executable. If it fails, restore the old address
	 * space and (re-)activate it.
	 */
	result = load_elf(v, entrypoint);
	if (result) {
		vfs_close(v);
		proc_setas(oldvm);
		as_activate();
		as_destroy(newvm);
		kfree(newname);
		return result;
	}

	vfs_close(v);

	/* Define the user stack in the address space */
	result = as_define_stack(newvm, stackptr);
	if (result) {
		proc_setas(oldvm);
		as_activate();
		as_destroy(newvm);
		kfree(newname);
		return result;
        }

	/*
	 * Wipe out old address space.
	 *
	 * Note: once this is done, execv() must not fail, because there's
	 * nothing left for it to return an error to.
	 */
	if (oldvm) {
		as_destroy(oldvm);
	}

	/*
	 * Now that we know we're succeeding, change the current thread's
	 * name to reflect the new process.
	 */
	kfree(curthread->t_name);
	curthread->t_name = newname;

	return 0;
}


/*
 * Open a file on a selected file descriptor. Takes care of various
 * minutiae, like the vfs-level open destroying pathnames.
 */
static
int
placed_open(const char *path, int openflags, int fd)
{
	struct openfile *newfile, *oldfile;
	char mypath[32];
	int result;

	/*
	 * The filename comes from the kernel, in fact right in this
	 * file; assume reasonable length. But make sure we fit.
	 */
	KASSERT(strlen(path) < sizeof(mypath));
	strcpy(mypath, path);

	result = openfile_open(mypath, openflags, 0664, &newfile);
	if (result) {
		return result;
	}

	/* place the file in the filetable in the right slot */
	filetable_placeat(curproc->p_filetable, newfile, fd, &oldfile);

	/* the table should previously have been empty */
	KASSERT(oldfile == NULL);

	return 0;
}

/*
 * Open the standard file descriptors: stdin, stdout, stderr.
 *
 * Note that if we fail part of the way through we can leave the fds
 * we've already opened in the file table and they'll get cleaned up
 * by process exit.
 */
static
int
open_stdfds(const char *inpath, const char *outpath, const char *errpath)
{
	int result;

	result = placed_open(inpath, O_RDONLY, STDIN_FILENO);
	if (result) {
		return result;
	}

	result = placed_open(outpath, O_WRONLY, STDOUT_FILENO);
	if (result) {
		return result;
	}

	result = placed_open(errpath, O_WRONLY, STDERR_FILENO);
	if (result) {
		return result;
	}

	return 0;
}

/*
 * Load program "progname" and start running it in usermode.
 * Does not return except on error.
 *
 * Opens the standard file descriptors if necessary.
 *
 * Calls vfs_open on PROGNAME (via loadexec) and thus may destroy it,
 * so it needs to be mutable.
 */
int
runprogram(char *progname)
{
	struct argbuf kargv;
	vaddr_t entrypoint, stackptr;
	int argc;
	userptr_t uargv;
	int result;

	/* We must be a thread that can run in a user process. */
	KASSERT(curproc->p_pid >= PID_MIN && curproc->p_pid <= PID_MAX);

	/* We should be a new process. */
	KASSERT(proc_getas() == NULL);

	/* Set up stdin/stdout/stderr if necessary. */
	if (curproc->p_filetable == NULL) {
		curproc->p_filetable = filetable_create();
		if (curproc->p_filetable == NULL) {
			return ENOMEM;
		}

		result = open_stdfds("con:", "con:", "con:");
		if (result) {
			return result;
		}
	}

	/*
	 * Cons up argv.
	 */

	argbuf_init(&kargv);
	result = argbuf_fromkernel(&kargv, progname);
	if (result) {
		argbuf_cleanup(&kargv);
		return result;
	}

	/* Load the executable. Note: must not fail after this succeeds. */
	result = loadexec(progname, &entrypoint, &stackptr);
	if (result) {
		argbuf_cleanup(&kargv);
		return result;
	}

	result = argbuf_copyout(&kargv, &stackptr, &argc, &uargv);
	if (result) {
		/* If copyout fails, *we* messed up, so panic */
		panic("execv: copyout_args failed: %s\n", strerror(result));
	}

	/* free the space */
	argbuf_cleanup(&kargv);

	/* Warp to user mode. */
	enter_new_process(argc, uargv, NULL /*uenv*/, stackptr, entrypoint);

	/* enter_new_process does not return. */
	panic("enter_new_process returned\n");
	return EINVAL;
}

/*
 * execv.
 *
 * 1. Copy in the program name.
 * 2. Copy in the argv with copyin_args.
 * 3. Load the executable.
 * 4. Copy the argv out again with copyout_args.
 * 5. Warp to usermode.
 */
int
sys_execv(userptr_t prog, userptr_t uargv)
{
	char *path;
	struct argbuf kargv;
	vaddr_t entrypoint, stackptr;
	int argc;
	int result;

	path = kmalloc(PATH_MAX);
	if (!path) {
		return ENOMEM;
	}

	/* Get the filename. */
	result = copyinstr(prog, path, PATH_MAX, NULL);
	if (result) {
		kfree(path);
		return result;
	}

	/* get the argv strings. */

	argbuf_init(&kargv);

	result = argbuf_fromuser(&kargv, uargv);
	if (result) {
		argbuf_cleanup(&kargv);
		kfree(path);
		return result;
	}

	/* Load the executable. Note: must not fail after this succeeds. */
	result = loadexec(path, &entrypoint, &stackptr);
	if (result) {
		argbuf_cleanup(&kargv);
		kfree(path);
		return result;
	}

	/* don't need this any more */
	kfree(path);

	/* Send the argv strings to the process. */
	result = argbuf_copyout(&kargv, &stackptr, &argc, &uargv);
	if (result) {
		/* if copyout fails, *we* messed up, so panic */
		panic("execv: copyout_args failed: %s\n", strerror(result));
	}

	/* free the argv buffer space */
	argbuf_cleanup(&kargv);

	/* Warp to user mode. */
	enter_new_process(argc, uargv, NULL /*uenv*/, stackptr, entrypoint);

	/* enter_new_process does not return. */
	panic("enter_new_process returned\n");
	return EINVAL;
}
