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
 * File tables.
 */

#include <types.h>
#include <kern/errno.h>
#include <lib.h>
#include <openfile.h>
#include <filetable.h>


/*
 * Construct a filetable.
 */
struct filetable *
filetable_create(void)
{
	struct filetable *ft;
	int fd;

	ft = kmalloc(sizeof(struct filetable));
	if (ft == NULL) {
		return NULL;
	}

	/* the table starts empty */
	for (fd = 0; fd < OPEN_MAX; fd++) {
		ft->ft_openfiles[fd] = NULL;
	}

	return ft;
}

/*
 * Destroy a filetable.
 */
void
filetable_destroy(struct filetable *ft)
{
	int fd;

	KASSERT(ft != NULL);

	/* Close any open files. */
	for (fd = 0; fd < OPEN_MAX; fd++) {
		if (ft->ft_openfiles[fd] != NULL) {
			openfile_decref(ft->ft_openfiles[fd]);
			ft->ft_openfiles[fd] = NULL;
		}
	}
	kfree(ft);
}

/*
 * Clone a filetable, for use in fork.
 *
 * The underlying openfile objects are shared, not copied; this means
 * that the seek position is shared among file handles inherited
 * across forks. In Unix this means that shell operations like
 *
 *    (
 *       echo hi
 *       echo there
 *    ) > file
 *
 * produce the intended output instead of having the second echo
 * command overwrite the first.
 */
int
filetable_copy(struct filetable *src, struct filetable **dest_ret)
{
	struct filetable *dest;
	struct openfile *file;
	int fd;

	/* Copying the nonexistent table avoids special cases elsewhere */
	if (src == NULL) {
		*dest_ret = NULL;
		return 0;
	}

	dest = filetable_create();
	if (dest == NULL) {
		return ENOMEM;
	}

	/* share the entries */
	for (fd = 0; fd < OPEN_MAX; fd++) {
		file = src->ft_openfiles[fd];
		if (file != NULL) {
			openfile_incref(file);
		}
		dest->ft_openfiles[fd] = file;
	}

	*dest_ret = dest;
	return 0;
}

/*
 * Check if a file handle is in range.
 */
bool
filetable_okfd(struct filetable *ft, int fd)
{
	/* We have a fixed-size table so we don't need to check the size */
	(void)ft;

	return (fd >= 0 && fd < OPEN_MAX);
}

/*
 * Get an openfile from a filetable. Calls to filetable_get should be
 * matched by calls to filetable_put.
 *
 * This checks that the file handle is in range and fails rather than
 * returning a null openfile; it only yields files that are actually
 * open.
 */
int
filetable_get(struct filetable *ft, int fd, struct openfile **ret)
{
	struct openfile *file;

	if (!filetable_okfd(ft, fd)) {
		return EBADF;
	}

	file = ft->ft_openfiles[fd];
	if (file == NULL) {
		return EBADF;
	}

	*ret = file;
	return 0;
}

/*
 * Put a file handle back when done with it. This does not actually do
 * anything (other than crosscheck) but it's always good practice to
 * build things so when you take them out you put them back again
 * rather than dropping them on the floor. Then if you need to do
 * something at cleanup time you can put it in this function instead
 * of having to hunt for all the places to insert the new logic.
 *
 * (For example, if you have multithreaded processes you will need to
 * insert additional lock and/or refcount manipulations here and in
 * filetable_get.)
 *
 * The openfile should be the one returned from filetable_get. If you
 * want to manipulate the table so the assertion's no longer true, get
 * your own reference to the openfile (with openfile_incref) and call
 * filetable_put before mucking about.
 */
void
filetable_put(struct filetable *ft, int fd, struct openfile *file)
{
	KASSERT(ft->ft_openfiles[fd] == file);
}

/*
 * Place a file in a file table and return the descriptor. We always
 * use the smallest available descriptor, because Unix works that way.
 * (Unix works that way because in the days before dup2 was invented,
 * the behavior had to be defined explicitly in order to allow
 * manipulating stdin/stdout/stderr.)
 *
 * Consumes a reference to the openfile object. (That reference is
 * placed in the table.)
 */
int
filetable_place(struct filetable *ft, struct openfile *file, int *fd_ret)
{
	int fd;

	for (fd = 0; fd < OPEN_MAX; fd++) {
		if (ft->ft_openfiles[fd] == NULL) {
			ft->ft_openfiles[fd] = file;
			*fd_ret = fd;
			return 0;
		}
	}

	return EMFILE;
}

/*
 * Place a file in a file table at a specific location and return the
 * file previously at that location. The location must be in range.
 *
 * Consumes a reference to the passed-in openfile object; returns a
 * reference to the old openfile object (if not NULL); this should
 * generally be decref'd.
 *
 * Doesn't fail.
 *
 * Note that you can use this to place NULL in the filetable, which is
 * potentially handy.
 */
void
filetable_placeat(struct filetable *ft, struct openfile *newfile, int fd,
		  struct openfile **oldfile_ret)
{
	KASSERT(filetable_okfd(ft, fd));

	*oldfile_ret = ft->ft_openfiles[fd];
	ft->ft_openfiles[fd] = newfile;
}
