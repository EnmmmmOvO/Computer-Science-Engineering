# The in-kernel system call code path

1. What is the numerical value of the exception code for a MIPS system call (Hint: EX_SYS)?

See `kern/arch/mips/include/trapframe.h`, this is where various trapframe/exception handling definitions are.

```
/*
 * MIPS exception codes.
 */
#define EX_IRQ    0    /* Interrupt */
#define EX_MOD    1    /* TLB Modify (write to read-only page) */
#define EX_TLBL   2    /* TLB miss on load */
#define EX_TLBS   3    /* TLB miss on store */
#define EX_ADEL   4    /* Address error on load */
#define EX_ADES   5    /* Address error on store */
#define EX_IBE    6    /* Bus error on instruction fetch */
#define EX_DBE    7    /* Bus error on data load *or* store */
#define EX_SYS    8    /* Syscall */
#define EX_BP     9    /* Breakpoint */
#define EX_RI     10   /* Reserved (illegal) instruction */
#define EX_CPU    11   /* Coprocessor unusable */
#define EX_OVF    12   /* Arithmetic overflow */
```

2. How many bytes is an instruction in MIPS? (Answer this by reading syscall() carefully, not by looking somewhere else.)

See `kern/arch/mips/syscall/syscall.c`. Also observe the switch statement. This is the code that determines the system call invoked and the calls the appropriate routine in the kernel. Also observe the convention or prefixing the in-kernel implementation of a system call with `sys_`, which you should follow as well.

```
/*
* Now, advance the program counter, to avoid restarting
* the syscall over and over again.
*/

tf->tf_epc += 4;
```

3. What is the contents of the struct trapframe? Where is the struct trapframe that is passed into syscall() stored?

See `trapframe.h`. It contains the register contents of the user-level application at the time of the trap, plus a few of the status registers useful to the kernel. The trapframe is stored on this process/thread's stack. See the system call lecture for a detailed description of have the trapframe is set up.

4. What would be required to implement a system call that took more than 4 arguments?

There are basically two options here:

1. Create a specific convention between the stubs in the user-level C-library that uses some more registers in the register set as input arguments (as we have done for the system call number).
2. Alternatively, we could use the C-compiler calling convention, which places extra arguments on the userlevel stack. The operating system would then have to obtain the arguments from the applications stack. This has to be done very carefully as there is no guarantee the application has a valid user-level stack pointer when the system call is invoked.

5. What is the purpose of `userptr_t`?

Basically, `userptr_t` is the type of pointers to memory that are supplied by applications (which can't be trusted to be valid). We use this type to avoid accidentally dereferencing one of these unsafe pointers in our kernel code.

```
/*
 * Define userptr_t as a pointer to a one-byte struct, so it won't mix
 * with other pointers.
 */

struct __userptr { char _dummy; };
typedef struct __userptr *userptr_t;
typedef const struct __userptr *const_userptr_t;
```

# UIOs and data transfer between the kernel and applications

Read through the comments in `kern/include/uio.h` for a description of the framework OS/161 provide to safely transfer data to and from applications from and to the kernel respectively.

6. What is the difference between `UIO_USERISPACE` and `UIO_USERSPACE`? When should one use `UIO_SYSSPACE` instead?

This flag indicates the destination memory to the uio framework: the kernel is SYSSPACE, and the application is USERSPACE. If SYSSPACE is the destination, various validity check can be avoided - the kernel is trusted not to corrupt itself. USERISPACE is the flag is the data is actual code being loaded to eventually be run by the application - on real hardware, the framework would flush the CPU instruction cache to ensure it is consistent with the content of memory.

```
/* Source/destination. */
enum uio_seg {
        UIO_USERISPACE,                 /* User process code. */
        UIO_USERSPACE,                  /* User process data. */
        UIO_SYSSPACE,                   /* Kernel. */
};
```

7. Why can the struct uio that is used to read in an ELF segment be allocated on the stack in load_segment() (i.e., where is the destination memory for the read)?

The `uio` is only metadata describing the destination or source of a data transfer. It can be on the stack as it is private to the kernel, the actual destination of load segment it the point in the iovec struct.

```
struct iovec {

#ifdef _KERNEL
        union {
                userptr_t  iov_ubase;   /* user-supplied pointer */
                void      *iov_kbase;   /* kernel-supplied pointer */
        };
#else
        void *iov_base;                 /* user-supplied pointer */
#endif
        size_t iov_len;                 /* Length of data */
};

struct uio {
        struct iovec     *uio_iov;      /* Data blocks */
        unsigned          uio_iovcnt;   /* Number of iovecs */
        off_t             uio_offset;   /* Desired offset into object */
        size_t            uio_resid;    /* Remaining amt of data to xfer */
        enum uio_seg      uio_segflg;   /* What kind of pointer we have */
        enum uio_rw       uio_rw;       /* Whether op is a read or write */
        struct addrspace *uio_space;    /* Address space for user pointer */
};
```

See the sample initialisation in `load_segment`.

```
        iov.iov_ubase = (userptr_t)vaddr;
        iov.iov_len = memsize;           // length of the memory space
        u.uio_iov = &iov;
        u.uio_iovcnt = 1;
        u.uio_resid = filesize;          // amount to read from the file
        u.uio_offset = offset;
        u.uio_segflg = is_executable ? UIO_USERISPACE : UIO_USERSPACE;
        u.uio_rw = UIO_READ;
        u.uio_space = as;
```

8. In what file are copyin() and copyout() defined? memmove()? Why can't copyin() and copyout() be implemented as simply as memmove()?

Read the comment at the top of `kern/vm/copyinout.c`. `memmove()` can't be used to copy data from/to applications as it has no way to recover if a fault occurs during the copy.

# VFS

9. How are vfs_open, vfs_close used? What other vfs_() calls are relevant?

vfs_open/vfs_close implement most of the work needed to implement the system calls open()/close(). You should read the man page for open and close to understand their semantics, then take a look at vfs_open/vfs_close to see how they relate. The remain vfs operations required for this assignment are the VOP_* functions.

10. What are VOP_READ, VOP_WRITE? How are they used?

They are the implementation of read and write for the filesystem. The main thing to understand here is how to use the uio struct to specify the source or destination of the write or read.

```
 *****************************************
 *
 *    vop_read        - Read data from file to uio, at offset specified
 *                      in the uio, updating uio_resid to reflect the
 *                      amount read, and updating uio_offset to match.
 *                      Not allowed on directories or symlinks.
 *
 *    vop_write       - Write data from uio to file at offset specified
 *                      in the uio, updating uio_resid to reflect the
 *                      amount written, and updating uio_offset to match.
 *                      Not allowed on directories or symlinks.
```

11. What does VOP_ISSEEKABLE do?

It returns whether the vnode is seekable (via lseek()). If not lseek can return an error, if seekable, lseek should update your file pointer.

# Fork

12. Where is the struct thread defined? What does this structure contain?

```
/* Thread structure. */
struct thread {
        /*
         * These go up front so they're easy to get to even if the
         * debugger is messed up.
         */
        char *t_name;                   /* Name of this thread */
        const char *t_wchan_name;       /* Name of wait channel, if sleeping */
        threadstate_t t_state;          /* State this thread is in */

        /*
         * Thread subsystem internal fields.
         */
        struct thread_machdep t_machdep; /* Any machine-dependent goo */
        struct threadlistnode t_listnode; /* Link for run/sleep/zombie lists */
        void *t_stack;                  /* Kernel-level stack */
        struct switchframe *t_context;  /* Saved register context (on stack) */
        struct cpu *t_cpu;              /* CPU thread runs on */
        struct proc *t_proc;            /* Process thread belongs to */

        /*
         * Interrupt state fields.
         *
         * t_in_interrupt is true if current execution is in an
         * interrupt handler, which means the thread's normal context
         * of execution is stopped somewhere in the middle of doing
         * something else. This makes assorted operations unsafe.
         *
         * See notes in spinlock.c regarding t_curspl and t_iplhigh_count.
         *
         * Exercise for the student: why is this material per-thread
         * rather than per-cpu or global?
         */
        bool t_in_interrupt;            /* Are we in an interrupt? */
        int t_curspl;                   /* Current spl*() state */
        int t_iplhigh_count;            /* # of times IPL has been raised */

        /*
         * Public fields
         */

        /* add more here as needed */
};
```

13. Where is the struct proc defined? What does this structure contain?

```
/*
 * Process structure.
 */
struct proc {
        char *p_name;                   /* Name of this process */
        struct spinlock p_lock;         /* Lock for this structure */
        struct threadarray p_threads;   /* Threads in this process */

        /* VM */
        struct addrspace *p_addrspace;  /* virtual address space */

        /* VFS */
        struct vnode *p_cwd;            /* current working directory */

        /* add more material here as needed */
};
```

14. What are the ELF magic numbers?

See elf.h:

```
/* For e_ident[EI_MAG0..3] */
#define ELFMAG0         0x7f
#define ELFMAG1         'E'
#define ELFMAG2         'L'
#define ELFMAG3         'F'
```

These numbers are used as a sanity check to validate an elf file.

15. In runprogram(), why is it important to call vfs_close before going to usermode?

After switching to the user application, runprogram never returns. Thus vfs_close must be called to avoid a memory leak.

16. What function forces the processor to switch into usermode? Is this function machine dependent?

`mips_usermode()`. Yes.

See the following code fragment for an example from `kern/arch/mips/locore/trap.c`

```
void
enter_new_process(int argc, userptr_t argv, userptr_t env,
                  vaddr_t stack, vaddr_t entry)
{
        struct trapframe tf;

        bzero(&tf, sizeof(tf));

        tf.tf_status = CST_IRQMASK | CST_IEp | CST_KUp;
        tf.tf_epc = entry;
        tf.tf_a0 = argc;
        tf.tf_a1 = (vaddr_t)argv;
        tf.tf_a2 = (vaddr_t)env;
        tf.tf_sp = stack;

        mips_usermode(&tf);
}
```

17. What is the purpose of the fork() system call?

To duplicate the current process, with the new child process starting at the same pc as the parent, just after the fork syscall is executed. For more detail see man/syscall/fork.html.

18. What process state is shared between the parent and child?

Open file table entries (including the file pointer) that were opened prior to the fork() call.

19. What process state is copied between the parent and child?

File descriptor tables (i.e. the per-process mapping between file-descriptors and open files) and memory.

20. What is the purpose of the SYSCALL macro?

It defines the syscall stubs, see userland/lib/libc/arch/mips/syscalls-mips.S.

21. What is the MIPS instruction that actually triggers a system call? (Answer this by reading the source in this directory, not looking somewhere else.)

See line 83 of userland/lib/libc/arch/mips/syscalls-mips.S.