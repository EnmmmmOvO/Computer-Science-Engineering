/*
 * Declarations for file handle and file table management.
 */

#ifndef _FILE_H_
#define _FILE_H_

/*
 * Contains some file-related maximum length constants
 */
#include <limits.h>


/*
 * Put your function declarations and data types here ...
 */
struct of {
    struct vnode *of_vnode;
    off_t of_offset;
    int of_permission;
    int of_count;
    struct lock *of_lock;
};

struct ft {
    struct of *ft_of[OPEN_MAX];
    struct lock *ft_lock;
};

int sys_open(const char *filename, int flags, mode_t mode, int *retval);
int sys_close(int fd);
int sys_read(int fd, void *buf, size_t buflen, int *retval);
int sys_write(int fd, const void *buf, size_t buflen, int *retval);
int sys_lseek(int fd, off_t pos, int whence, off_t *retval);
int sys_dup2(int oldfd, int newfd);

// FileTable Support Function
struct ft *create_ft(void);
void destroy_ft(struct ft *ft);
int add_ft(struct ft *ft, struct of *of, int *fd_return);
int del_ft(struct ft *ft, int fd, struct of **of_return);
int get_ft(struct ft *ft, int fd, struct of **ret);

// OpenFile Support Function
struct of *create_of(struct vnode *vn, int flags);
void increase_of(struct of *of);
void decrease_of(struct of *of);
void destroy_of(struct of *of);




#endif /* _FILE_H_ */
