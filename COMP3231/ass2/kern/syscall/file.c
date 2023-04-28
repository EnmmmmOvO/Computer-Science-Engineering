#include <types.h>
#include <kern/errno.h>
#include <kern/fcntl.h>
#include <kern/limits.h>
#include <kern/stat.h>
#include <kern/seek.h>
#include <lib.h>
#include <uio.h>
#include <proc.h>
#include <current.h>
#include <synch.h>
#include <vfs.h>
#include <vnode.h>
#include <file.h>
#include <syscall.h>
#include <copyinout.h>

/*
 * Add your file-related functions here ...
 */

int sys_open(const char *filename, int flags, mode_t mode, int *retval) {
    char *kern_filename = kmalloc(sizeof(char) * PATH_MAX);
    if (kern_filename == NULL) {
        return ENOMEM;
    }

    int result = copyinstr((const_userptr_t)filename, kern_filename, PATH_MAX, NULL);
    if (result) {
        kfree(kern_filename);
        return result;
    }

    struct vnode *vn;
    result = vfs_open(kern_filename, flags, mode, &vn);
    if (result) {
        kfree(kern_filename);
        return result;
    }

    struct of *of = create_of(vn, flags);
    if (of == NULL) {
        vfs_close(vn);
        kfree(kern_filename);
        return ENOMEM;
    }

    result = add_ft(curproc->p_ft, of, retval);
    if (result) {
        decrease_of(of);
        kfree(kern_filename);
        return result;
    }

    kfree(kern_filename);
    return 0;
}

int sys_close(int fd) {
    struct of *of;
    struct ft *ft = curproc->p_ft;

    int result = del_ft(ft, fd, &of);
    if (result) return result;

    decrease_of(of);

    return 0;
}

int sys_read(int fd, void *buf, size_t buflen, int *retval) {
    struct of *of;

    int result = get_ft(curproc->p_ft, fd, &of);
    if (result) return result;

    if ((of->of_permission & O_ACCMODE) == O_WRONLY) {
        decrease_of(of);
        return EBADF;
    }

    struct iovec iov;
    struct uio u;
    uio_uinit(&iov, &u, buf, buflen, of->of_offset, UIO_READ);

    result = VOP_READ(of->of_vnode, &u);
    if (result) {
        decrease_of(of);
        return result;
    }

    of->of_offset = u.uio_offset;
    *retval = buflen - u.uio_resid;
    decrease_of(of);

    return 0;
}

int sys_write(int fd, const void *buf, size_t buflen, int *retval) {
    struct of *of;

    int result = get_ft(curproc->p_ft, fd, &of);
    if (result) return result;
    
    if ((of->of_permission & O_ACCMODE) == O_RDONLY) {
        decrease_of(of);
        return EBADF;
    }
    
    struct iovec iov;
    struct uio u;
    uio_uinit(&iov, &u, (void *)buf, buflen, of->of_offset, UIO_WRITE);

    result = VOP_WRITE(of->of_vnode, &u);
    if (result) {
        decrease_of(of);
        return result;
    }

    of->of_offset = u.uio_offset;
    *retval = buflen - u.uio_resid;
    decrease_of(of);

    return 0;
}

int sys_lseek(int fd, off_t pos, int whence, off_t *retval) {
    struct of *of;
    
    int result = get_ft(curproc->p_ft, fd, &of);
    if (result) return result;

    if (!VOP_ISSEEKABLE(of->of_vnode)) {
        decrease_of(of);
        return ESPIPE;
    }

    off_t new_offset;
    switch (whence) {
        case SEEK_SET: new_offset = pos; break;
        case SEEK_CUR: new_offset = of->of_offset + pos; break;
        case SEEK_END: {
            struct stat st;
            result = VOP_STAT(of->of_vnode, &st);
            if (result) {
                decrease_of(of);
                return result;
            }
            new_offset = st.st_size + pos;
            break;
        }
        default:
            decrease_of(of);
            return EINVAL;
    }

    if (new_offset < 0) {
        decrease_of(of);
        return EINVAL;
    }

    of->of_offset = new_offset;
    *retval = new_offset;
    decrease_of(of);

    return 0;
}

int sys_dup2(int oldfd, int newfd) {
    if (oldfd == newfd) return 0;
    else if (newfd < 0 || newfd >= OPEN_MAX) return EBADF;

    struct of *old_of;
    int result = get_ft(curproc->p_ft, oldfd, &old_of);
    if (result) return result;

    struct of *new_of;
    result = get_ft(curproc->p_ft, newfd, &new_of);
    if (result == 0) {
        del_ft(curproc->p_ft, newfd, &new_of);
        decrease_of(new_of);
    }

    increase_of(old_of);
    add_ft(curproc->p_ft, old_of, &newfd);
    decrease_of(old_of);

    return 0;
}

// FileTable Support Function
struct ft *create_ft(void) {
    struct ft *ft = kmalloc(sizeof(*ft));
    if (ft == NULL) return NULL;

    ft->ft_lock = lock_create("ft_lock");
    if (ft->ft_lock == NULL) {
        kfree(ft);
        return NULL;
    }

    char con[] = "con:";
    struct vnode *con_vnode;
    int result = vfs_open(con, O_RDWR, 0, &con_vnode);
    if (result) {
        lock_destroy(ft->ft_lock);
        kfree(ft);
        return NULL;
    }

    for (int i = 0; i < 3; i++) {
        ft->ft_of[i] = create_of(con_vnode, O_RDWR);
        if (ft->ft_of[i] == NULL) {
            for (int j = 0; j < i; j++) decrease_of(ft->ft_of[j]);
            vfs_close(con_vnode);
            lock_destroy(ft->ft_lock);
            kfree(ft);
            return NULL;
        }
        increase_of(ft->ft_of[i]);
    }
    vfs_close(con_vnode);

    for (int i = 3; i < OPEN_MAX; i++) ft->ft_of[i] = NULL;

    return ft;
}

void destroy_ft(struct ft *ft) {
    KASSERT(ft != NULL);

    lock_acquire(ft->ft_lock);

    for (int i = 0; i < OPEN_MAX; i++) {
        if (ft->ft_of[i] != NULL) {
            decrease_of(ft->ft_of[i]);
            ft->ft_of[i] = NULL;
        }
    }

    lock_release(ft->ft_lock);
    lock_destroy(ft->ft_lock);
    kfree(ft);
}

int add_ft(struct ft *ft, struct of *of, int *fd) {
    KASSERT(ft != NULL);
    KASSERT(of != NULL);
    KASSERT(fd != NULL);

    lock_acquire(ft->ft_lock);

    for (int i = 0; i < OPEN_MAX; i++) {
        if (ft->ft_of[i] == NULL) {
            ft->ft_of[i] = of;
            increase_of(of);
            *fd = i;
            lock_release(ft->ft_lock);
            return 0;
        }
    }

    lock_release(ft->ft_lock);
    return EMFILE;
}

int del_ft(struct ft *ft, int fd, struct of **of_return) {
    KASSERT(ft != NULL);
    KASSERT(of_return != NULL);

    if (fd < 0 || fd >= OPEN_MAX) return EBADF;

    lock_acquire(ft->ft_lock);

    if (ft->ft_of[fd] == NULL) {
        lock_release(ft->ft_lock);
        return EBADF;
    }

    *of_return = ft->ft_of[fd];
    ft->ft_of[fd] = NULL;
    lock_release(ft->ft_lock);

    return 0;
}

int get_ft(struct ft *ft, int fd, struct of **ret) {
    KASSERT(ft != NULL);

    if (fd < 0 || fd >= OPEN_MAX) return EBADF;

    lock_acquire(ft->ft_lock);

    struct of *of = ft->ft_of[fd];

    if (of == NULL) {
        lock_release(ft->ft_lock);
        return EBADF;
    }

    increase_of(of);
    *ret = of;
    lock_release(ft->ft_lock);

    return 0;
}

// OpenFile Support Function
struct of *create_of(struct vnode *vn, int flags) {
    KASSERT(vn != NULL);

    struct of *of = kmalloc(sizeof(*of));
    if (of == NULL) return NULL;

    of->of_vnode = vn;
    of->of_offset = 0;
    of->of_permission = flags & O_ACCMODE;
    of->of_count = 1; 
    of->of_lock = lock_create("openfile_lock");

    if (of->of_lock == NULL) {
        kfree(of);
        return NULL;
    }

    return of;
}

void increase_of(struct of *of) {
    KASSERT(of != NULL);

    lock_acquire(of->of_lock);
    of->of_count++;         
    lock_release(of->of_lock);
}

void decrease_of(struct of *of) {
    KASSERT(of != NULL);

    lock_acquire(of->of_lock);
    of->of_count--;
    lock_release(of->of_lock);

    if (of->of_count == 0) destroy_of(of);
}

void destroy_of(struct of *of) {
    lock_acquire(of->of_lock);
    vfs_close(of->of_vnode);
    lock_release(of->of_lock);
    lock_destroy(of->of_lock);
    kfree(of);   
}
