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
 * File table management.
 */

#ifndef _FILETABLE_H_
#define _FILETABLE_H_

#include <limits.h> /* for OPEN_MAX */


/*
 * The file table is an array of open files.
 *
 * There is no particular reason to use a fixed size array (of size
 * OPEN_MAX) instead of a dynamically sized array (using array.h) --
 * the code was just written this way years ago and there's no
 * compelling reason to change it that outweighs this benefit: you can
 * look through the code to see what it would take to make it dynamic,
 * or even to make it dynamic with the limit being user-settable. (See
 * setrlimit(2) on a Unix machine.)
 *
 * Because we only have single-threaded processes, the file table is
 * never shared and so it doesn't require synchronization. On fork,
 * the table is copied. Another exercise: what would you need to do to
 * make this code safe for multithreaded processes? What happens if
 * one thread calls close() while another one is in the middle of e.g.
 * read() using the same file handle?
 */
struct filetable {
	struct openfile *ft_openfiles[OPEN_MAX];
};

/*
 * Filetable ops:
 *
 * create -  Construct an empty file table.
 * destroy - Wipe out a file table, closing anything open in it.
 * copy -    Clone a file table.
 * okfd -    Check if a file handle is in range.
 * get/put - Retrieve a fd for use and put it back when done. (Checks
 *           okfd and also fails on files not open; returned openfile
 *           is not NULL.) Call put with the file returned from get.
 * place -   Insert a file and return the fd.
 * placeat - Insert a file at a specific slot and return the file
 *           previously there.
 */

struct filetable *filetable_create(void);
void filetable_destroy(struct filetable *ft);
int filetable_copy(struct filetable *src, struct filetable **dest_ret);

bool filetable_okfd(struct filetable *ft, int fd);
int filetable_get(struct filetable *ft, int fd, struct openfile **ret);
void filetable_put(struct filetable *ft, int fd, struct openfile *file);

int filetable_place(struct filetable *ft, struct openfile *file, int *fd);
void filetable_placeat(struct filetable *ft, struct openfile *newfile, int fd,
		       struct openfile **oldfile_ret);


#endif /* _FILETABLE_H_ */
