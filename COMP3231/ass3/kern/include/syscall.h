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

#ifndef _SYSCALL_H_
#define _SYSCALL_H_


#include <cdefs.h> /* for __DEAD */
struct trapframe; /* from <machine/trapframe.h> */

/*
 * The system call dispatcher.
 */

void syscall(struct trapframe *tf);

/*
 * Support functions.
 */

/* Helper for fork(). You write this. */
void enter_forked_process(struct trapframe *tf);

/* Enter user mode. Does not return. */
__DEAD void enter_new_process(int argc, userptr_t argv, userptr_t env,
		       vaddr_t stackptr, vaddr_t entrypoint);

/* Setup function for exec. */
void exec_bootstrap(void);


/*
 * Prototypes for IN-KERNEL entry points for system call implementations.
 *
 * Note that we use userptr_t's for userspace pointers, so that there
 * isn't any confusion about what space the pointers are in.
 */

int sys_reboot(int code);
int sys___time(userptr_t user_seconds, userptr_t user_nanoseconds);

int sys_fork(struct trapframe *tf, pid_t *retval);
int sys_execv(userptr_t prog, userptr_t args);
__DEAD void sys__exit(int code);
int sys_waitpid(pid_t pid, userptr_t returncode, int flags, pid_t *retval);
int sys_getpid(pid_t *retval);

int sys_open(const_userptr_t filename, int flags, mode_t mode, int *retval);
int sys_dup2(int oldfd, int newfd, int *retval);
int sys_close(int fd);
int sys_read(int fd, userptr_t buf, size_t size, int *retval);
int sys_write(int fd, userptr_t buf, size_t size, int *retval);
int sys_lseek(int fd, off_t offset, int code, off_t *retval);

int sys_chdir(const_userptr_t path);
int sys___getcwd(userptr_t buf, size_t buflen, int *retval);

int sys_sync(void);
int sys_mkdir(userptr_t path, mode_t mode);
int sys_rmdir(userptr_t path);
int sys_remove(userptr_t path);
int sys_link(userptr_t oldpath, userptr_t newpath);
int sys_rename(userptr_t oldpath, userptr_t newpath);
int sys_getdirentry(int fd, userptr_t buf, size_t buflen, int *retval);
int sys_fstat(int fd, userptr_t statptr);
int sys_fsync(int fd);
int sys_ftruncate(int fd, off_t len);

#endif /* _SYSCALL_H_ */
