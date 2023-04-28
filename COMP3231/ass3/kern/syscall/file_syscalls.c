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
 * File-related system call implementations.
 */

#include <types.h>
#include <kern/errno.h>
#include <kern/fcntl.h>
#include <kern/limits.h>
#include <kern/seek.h>
#include <kern/stat.h>
#include <lib.h>
#include <uio.h>
#include <proc.h>
#include <current.h>
#include <synch.h>
#include <copyinout.h>
#include <vfs.h>
#include <vnode.h>
#include <openfile.h>
#include <filetable.h>
#include <syscall.h>

/*
 * open() - get the path with copyinstr, then use openfile_open and
 * filetable_place to do the real work.
 */
int
sys_open(const_userptr_t upath, int flags, mode_t mode, int *retval)
{
	const int allflags =
		O_ACCMODE | O_CREAT | O_EXCL | O_TRUNC | O_APPEND | O_NOCTTY;

	char *kpath;
	struct openfile *file;
	int result;

	if ((flags & allflags) != flags) {
		/* unknown flags were set */
		return EINVAL;
	}

	kpath = kmalloc(PATH_MAX);
	if (kpath == NULL) {
		return ENOMEM;
	}

	/* Get the pathname. */
	result = copyinstr(upath, kpath, PATH_MAX, NULL);
	if (result) {
		kfree(kpath);
		return result;
	}

	/*
	 * Open the file. Code lower down (in vfs_open) checks that
	 * flags & O_ACCMODE is a valid value.
	 */
	result = openfile_open(kpath, flags, mode, &file);
	if (result) {
		kfree(kpath);
		return result;
	}
	kfree(kpath);

	/*
	 * Place the file in our process's file table, which gives us
	 * the result file descriptor.
	 */
	result = filetable_place(curproc->p_filetable, file, retval);
	if (result) {
		openfile_decref(file);
		return result;
	}

	return 0;
}

/*
 * Common logic for read and write.
 *
 * Look up the fd, then use VOP_READ or VOP_WRITE.
 */
static
int
sys_readwrite(int fd, userptr_t buf, size_t size, enum uio_rw rw,
	      int badaccmode, ssize_t *retval)
{
	struct openfile *file;
	bool locked;
	off_t pos;
	struct iovec iov;
	struct uio useruio;
	int result;

	/* better be a valid file descriptor */
	result = filetable_get(curproc->p_filetable, fd, &file);
	if (result) {
		return result;
	}

	/* Only lock the seek position if we're really using it. */
	locked = VOP_ISSEEKABLE(file->of_vnode);
	if (locked) {
		lock_acquire(file->of_offsetlock);
		pos = file->of_offset;
	}
	else {
		pos = 0;
	}

	if (file->of_accmode == badaccmode) {
		result = EBADF;
		goto fail;
	}

	/* set up a uio with the buffer, its size, and the current offset */
	uio_uinit(&iov, &useruio, buf, size, pos, rw);

	/* do the read or write */
	result = (rw == UIO_READ) ?
		VOP_READ(file->of_vnode, &useruio) :
		VOP_WRITE(file->of_vnode, &useruio);
	if (result) {
		goto fail;
	}

	if (locked) {
		/* set the offset to the updated offset in the uio */
		file->of_offset = useruio.uio_offset;
		lock_release(file->of_offsetlock);
	}

	filetable_put(curproc->p_filetable, fd, file);

	/*
	 * The amount read (or written) is the original buffer size,
	 * minus how much is left in it.
	 */
	*retval = size - useruio.uio_resid;

	return 0;

fail:
	if (locked) {
		lock_release(file->of_offsetlock);
	}
	filetable_put(curproc->p_filetable, fd, file);
	return result;
}

/*
 * read() - use sys_readwrite
 */
int
sys_read(int fd, userptr_t buf, size_t size, int *retval)
{
	return sys_readwrite(fd, buf, size, UIO_READ, O_WRONLY, retval);
}

/*
 * write() - use sys_readwrite
 */
int
sys_write(int fd, userptr_t buf, size_t size, int *retval)
{
	return sys_readwrite(fd, buf, size, UIO_WRITE, O_RDONLY, retval);
}

/*
 * close() - remove from the file table.
 */
int
sys_close(int fd)
{
	struct filetable *ft;
	struct openfile *file;

	ft = curproc->p_filetable;

	/* check if the file's in range before calling placeat */
	if (!filetable_okfd(ft, fd)) {
		return EBADF;
	}

	/* place null in the filetable and get the file previously there */
	filetable_placeat(ft, NULL, fd, &file);

	if (file == NULL) {
		/* oops, it wasn't open, that's an error */
		return EBADF;
	}

	/* drop the reference */
	openfile_decref(file);
	return 0;
}

/*
 * lseek() - manipulate the seek position.
 */
int
sys_lseek(int fd, off_t offset, int whence, off_t *retval)
{
	struct stat info;
	struct openfile *file;
	int result;

	/* Get the open file. */
	result = filetable_get(curproc->p_filetable, fd, &file);
	if (result) {
		return result;
	}

	/* If it's not a seekable object, forget about it. */
	if (!VOP_ISSEEKABLE(file->of_vnode)) {
		filetable_put(curproc->p_filetable, fd, file);
		return ESPIPE;
	}

	/* Lock the seek position. */
	lock_acquire(file->of_offsetlock);

	/* Compute the new position. */
	switch (whence) {
	    case SEEK_SET:
		*retval = offset;
		break;
	    case SEEK_CUR:
		*retval = file->of_offset + offset;
		break;
	    case SEEK_END:
		result = VOP_STAT(file->of_vnode, &info);
		if (result) {
			lock_release(file->of_offsetlock);
			filetable_put(curproc->p_filetable, fd, file);
			return result;
		}
		*retval = info.st_size + offset;
		break;
	    default:
		lock_release(file->of_offsetlock);
		filetable_put(curproc->p_filetable, fd, file);
		return EINVAL;
	}

	/* If the resulting position is negative (which is invalid) fail. */
	if (*retval < 0) {
		lock_release(file->of_offsetlock);
		filetable_put(curproc->p_filetable, fd, file);
		return EINVAL;
	}

	/* Success -- update the file structure with the new position. */
	file->of_offset = *retval;

	lock_release(file->of_offsetlock);
	filetable_put(curproc->p_filetable, fd, file);

	return 0;
}

/*
 * dup2() - clone a file descriptor.
 */
int
sys_dup2(int oldfd, int newfd, int *retval)
{
	struct filetable *ft;
	struct openfile *oldfdfile, *newfdfile;
	int result;

	ft = curproc->p_filetable;

	if (!filetable_okfd(ft, newfd)) {
		return EBADF;
	}

	/* dup2'ing an fd to itself automatically succeeds (BSD semantics) */
	if (oldfd == newfd) {
		*retval = newfd;
		return 0;
	}

	/* get the file */
	result = filetable_get(ft, oldfd, &oldfdfile);
	if (result) {
		return result;
	}

	/* make another reference and return the fd */
	openfile_incref(oldfdfile);
	filetable_put(ft, oldfd, oldfdfile);

	/* place it */
	filetable_placeat(ft, oldfdfile, newfd, &newfdfile);

	/* if there was a file already there, drop that reference */
	if (newfdfile != NULL) {
		openfile_decref(newfdfile);
	}

	/* return newfd */
	*retval = newfd;
	return 0;
}

/*
 * chdir() - change directory. Send the path off to the vfs layer.
 */
int
sys_chdir(const_userptr_t path)
{
	char *pathbuf;
	int result;

	pathbuf = kmalloc(PATH_MAX);
	if (pathbuf == NULL) {
		return ENOMEM;
	}

	result = copyinstr(path, pathbuf, PATH_MAX, NULL);
	if (result) {
		kfree(pathbuf);
		return result;
	}

	result = vfs_chdir(pathbuf);
	kfree(pathbuf);
	return result;
}

/*
 * __getcwd() - get current directory. Make a uio and get the data
 * from the VFS code.
 */
int
sys___getcwd(userptr_t buf, size_t buflen, int *retval)
{
	struct iovec iov;
	struct uio useruio;
	int result;

	uio_uinit(&iov, &useruio, buf, buflen, 0, UIO_READ);

	result = vfs_getcwd(&useruio);
	if (result) {
		return result;
	}

	*retval = buflen - useruio.uio_resid;
	return 0;
}
