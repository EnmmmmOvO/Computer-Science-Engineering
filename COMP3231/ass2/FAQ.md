# Assignment 2

## FAQ and other Gotchas

### What should I do with stdin?

You can do as the spec says, i.e. nothing. File descriptor 0 at the start of the program can start closed. Yes, subsequent calls to open can validly return 0 as the fd allocated.

### How do I connect the console to stdout and stderr?

They need to open the `"con:"` device and arrange for fd 1 and fd 2 to refer to that device.

File descriptors 1 and 2 (from the applications perspective) need to be already open and connected to the device `"con:"`.

note that

```
v1 = vfs_open("con:"); 
v2 = vfs_open("con:"); 
```

does not work as the two strings `"con:"` are stored as a single string in memory, and it is overwritten in memory by the first call to `vfs_open()`. The following is okay as is declares two strings stored separately in memory.

```
char conname[5];
 
strcpy(conname,"con:");
r1 = vfs_open(conname,f1,m1,&v1);

strcpy(conname,"con:"); 
r2 = vfs_open(conname,f2,m2,&v2);
```

Alternatively, you can understand and use the reference counts inside vnodes to use the same vnode twice.

### What order should I allocate the file descriptors on an open() call

For the purposes of the assignment, it does not matter. However, the usual method is the lowest free descriptor.

### How do I find the current process?

There is a `curproc` macro that always provides a pointer to the `struct proc` of the current process.

### How do I find the end of the file for lseek() ?

`VOP_STAT()` will give you the current file size which you can assume is the end of the file.

### What do I have to do to implement O_APPEND

Nothing specific - just pass the flag to `vfs_open()` - it is the underlying filesystem's responsibility to implement `O_APPEND`, which it does not for emufs and sfs in our case.

### Can applications close stdout and stderr?

Yes, stdout, stderr (and stdin) can be closed like normal files, and the file descriptor can be re-used when opening new files.

### Are OS/161 applications single-threaded or multi-threaded

You can assume they are single threaded.

### lseek() has a 64-bit offset, how are the arguments passed?

See the long comment at the top of `kern/arch/mips/syscall/syscall.c`. It describes the argument passing convention when 64-bit int are involved.

Also see `join32to64()` and `split64to32()` in `kern/lib/bswap.c`. These two files give you enough info and support machinery to deal with off_t relatively simply.

The following fragment of code might prove useful.

```
uint64_t offset;
int whence;
off_t retval64;
        
join32to64(tf->tf_a2, tf->tf_a3, &offset);

copyin((userptr_t)tf->tf_sp + 16, &whence, sizeof(int));

split64to32(retval64, &tf->tf_v0, &tf->tf_v1);
```

### What is the minimum number of open files that should be supported?

You should support at least 128 open files in your open file table, if it is a statically sized table; if it is dynamically allocated, assume there will be enough memory from kmalloc not to fail for our auto-testing (assuming you don't allocate huge excess memory).

If too many files are open within a particular process, you should return EMFILE. If too many files are open systemwide, you should return ENFILE.

The per-process file descriptor table should be `OPEN_MAX` (128) in size.

### File descriptor table gotcha for fork()

Remember to copy across the file descriptor table so that your test for the child thread actually prints something out (no, it's not hanging)

### What is the minimum number of processes that should be supported for fork()?

You should support the existence of at least 64 processes at a time.

### Basic pointer arithmetic

Something to beware of:

```
char *x = (char*)0x12345678;
int *y = (int*)0x12345678;
x++;
y++;
```

x will be 0x12345679, y will be 0x1234567C. i.e. the compiler will automatically increment it by the size of the type it points to

### Local variables vs kmalloc

Don't create large local arrays. They will be put on the stack, which is tiny. For large arrays, use kmalloc. Then they go on the heap, which has much more space. In particular, don't create a local array of size ARG_MAX (I think it's 4k, which is the same size as the stack so is guaranteed to overflow it?)

### Why am I getting "emu0: got fatal result code 2"?

[emufs](http://os161.eecs.harvard.edu/documentation/sys161-2.0.8/devices.html#emufs) is a special device on the sys161 bus that presents a device that accesses the underlying filesystem of the machine hosting the sys161 virtual machine. sys161 passes these requests through to the host operating system via native calls to open, read, write and close. "fatal result code 2" means "bad handle" i.e. the sys161 emulator does not have an host FD open for the provided handle. This can happen if a file is closed prematurely (perhaps because the your reference count is not being maintained correctly).