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
 * File handles.
 */

#ifndef _OPENFILE_H_
#define _OPENFILE_H_

#include <spinlock.h>


/*
 * Structure for open files.
 *
 * This is pretty much just a wrapper around a vnode; the important
 * additional things we keep here are the open mode and the file's
 * seek position.
 *
 * Open files are reference-counted because they get shared via fork
 * and dup2 calls. And they need locking because that sharing can be
 * among multiple concurrent processes.
 */
struct openfile {
	struct vnode *of_vnode;
	int of_accmode;	/* from open: O_RDONLY, O_WRONLY, or O_RDWR */

	struct lock *of_offsetlock;	/* lock for of_offset */
	off_t of_offset;

	struct spinlock of_reflock;	/* lock for of_refcount */
	int of_refcount;
};

/* open a file (args must be kernel pointers; destroys filename) */
int openfile_open(char *filename, int openflags, mode_t mode,
		  struct openfile **ret);

/* adjust the refcount on an openfile */
void openfile_incref(struct openfile *);
void openfile_decref(struct openfile *);


#endif /* _OPENFILE_H_ */
