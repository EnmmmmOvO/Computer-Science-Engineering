## Tutorial Week 7



#### Files and file systems

1. Why does Linux pre-allocate up to 8 blocks on a write to a file.

   > Pre-allocating provides better locality when many writes to independent files are interleaved.

2. Linux uses a *buffer cache* to improve performance. What is the drawback of such a cache? In what scenario is it problematic? What alternative would be more appropriate where a buffer cache is inappropriate?

   > The buffering writes in the buffer cache provides the opportunity for data to be lost if the system stops prior to the cache being flushed.
   >
   > Removable storage devices are particular problematic if users don't "unmount" them first.
   >
   > Robustness can be improved by using a write-through cache at the expense of poor write performance.

3. What is the structure of the contents of a directory? Does it contain attributes such as creation times of files? If not, where might this information be stored?

   > - See lecture slides.
   > - No, directories only have a name-to-inode mapping
   > - Attributes of the file are stored in the inode itself.

4. The Unix inode structure contains a reference count. What is the reference count for? Why can't we just remove the inode without checking the reference count when a file is deleted?

   > Inodes contain a reference count due to hard links. The reference count is equal to the number of directory entries that reference the inode. For hard-linked files, multiple directory entries reference a single inode. The inode must not be removed until no directory entries are left (ie, the reference count is 0) to ensure that the filesystem remains consistent.

5. Inode-based filesystems typically divide a file system partition into *block groups*. Each block group consists of a number of contiguous physical disk blocks. Inodes for a given block group are stored in the same physical location as the block groups. What are the advantages of this scheme? Are they any disadvantages?

   > - Each group contains a redundant superblock. This make the file system more robust to disk block failures.
   > - Block groups keep the inodes physically closer to the files they refer to than they would be (on average) on a system without block groups. Since accessing and updating files also involves accessing or updating its inode, having the inode and the file's block close together reduces disk seek time, and thus improves performance. The OS must take care that all blocks remain within the block group of their inode.

6. Assume an inode with 10 direct blocks, as well as single, double and triple indirect block pointers. Taking into account creation and accounting of the indirect blocks themselves, what is the largest possible number of block reads and writes in order to:

   1. Read 1 byte
   2. Write 1 byte

   Assume the inode is cached in memory.

   > 1. To write 1 byte, in the worst case:
   >    - 4 writes: create single indirect block, create double indirect block, create triple indirect block, write data block.
   >    - 3 reads, 2 writes: read single indirect, read double indirect, read triple indirect, write triple indirect, write data block
   >    - Other combinations are possible
   > 2. To read 1 byte, in the worst case:
   >    - 4 reads: read single indirect, read double indirect, read triple indirect, read data block

7. Assume you have an inode-based filesystem. The filesystem has 512 byte blocks. Each inode has 10 direct, 1 single indirect, 1 double indirect, and 1 triple indirect block pointer. Block pointers are 4 bytes each. Assume the inode and any block free list is always in memory. Blocks are not cached.

   1. What is the maximum file size that can be stored before

      1. the single indirect pointer is needed?
      2. the double indirect pointer is needed?
      3. the triple indirect pointer is needed?

      > 1. 5K
      > 2. 69K
      > 3. 8261K

   2. What is the maximum file size supported?

      > 1056837K

   3. What is the number of disk block reads required to read 1 byte from a file

      1. in the best case?
      2. in the worst case?

      > 1. 1
      > 2. 4

   4. What is the number of disk block reads and writes required to write 1 byte to a file

      1. in the best case?
      2. in the worst case?

      > 1. 1w
      > 2. 4r/1w

8. A typical UNIX inode stores both the file's size and the number of blocks currently used to store the file. Why store both? Should not blocks = size / block size?

   > Blocks used to store the file are only indirectly related to file size.
   >
   > - The blocks used to store a file includes and indirect blocks used by the filesystem to keep track of the file data blocks themselves.
   > - File systems only store blocks that actually contain file data. Sparsely populated files can have large regions that are unused within a file.

9. How can deleting a file leave a inode-based file system (like ext2fs in Linux) inconsistent in the presence of a power failure.

   > Deleting a file consists of three separate modifications to the disk:
   >
   > - Mark disk blocks as free.
   > - Remove the directory entry.
   > - Mark the i-node as free.
   >
   > If the system only completes a subset of the operations (due to power failures or the like), the file system is no longer consistent. See lecture slide for example of things that can go wrong.

10. How does adding journalling to a file system avoid corruption in the presence of unexpected power failures.

    > Simply speaking, adding a journal addresses the issue by grouping file system updates into transactions that should either completely fail or succeed. These transactions are logged prior to manipulating the file system. In the presence of failure the transaction can be completed by replaying the updates remaining in the log.