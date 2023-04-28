# FAQs and other gotchas

## Make sure you zero out new pages

When you allocate a new frame to back a new page in an application, the application expects uninitialized memory to be zero, so you need to zero out the new frames before mapping them in a process.

## Don't use kprintf style debugging in the TLB refill routine

kprintf causes a context switch (it blocks) which flushes the TLB, which potentially ejects the entry you have just loaded - infinite loop, here we come. A more detailed discussion on kprintf can be found here https://www.cse.unsw.edu.au/~learn/debugging/modules/kprintf/.

Use `trace161 -t t kernel` instead to see TLB activity. See https://www.cse.unsw.edu.au/~learn/debugging/modules/trace_161/ for further details.

## How to I enforce the read/write/execute region permissions on pages

The MIPS does not have an execute bit, nor an independent writable bit. So aim to ensure a page has at least the minimum permissions needed for the region, which sometimes results in more permissions than specified.

Here is a sample between read (r), write (w), execute (x) permissions associated with regions, and the page table bits for writable (TLB_DIRTY : D) and valid (TLB_VALID: V)

```C
rwx = DV
rw- = DV
r-x = -V
r-- = -V
-wx = DV
-w- = DV
--x = -V
--- = --
```

# Testing

## What existing tests are available for testing our VM?

- testbin/huge

```C
OS/161$ p /testbin/huge
Entering the huge program - I will stress test your VM
stage [1] done
stage [2.0] done
stage [2.1] done
stage [2.2] done
stage [2.3] done
stage [2.4] done
stage [2] done
You passed!
/bin/sh: subprocess time: 1.043204385 seconds
OS/161$
```

- testbin/faulter

```C
OS/161$ p /testbin/faulter

Entering the faulter program - I should die immediately
Fatal user mode trap 2 sig 11 (TLB miss on load, epc 0x4000c8, vaddr 0x40000000)
/bin/sh: subprocess time: 0.357791889 seconds
Signal 11
OS/161$
```

- testbin/triplehuge

```C
OS/161$ p /testbin/triplehuge
/testbin/triplehuge: Starting: running three copies of /testbin/huge...
Entering the huge program - I will stress test your VM
Entering the hEntering the huge program - I will stress test your VM
uge program - I will stress test your VM
stage [1] done
stage [1] done
stage [2.0] done
stage [2.0] done
stage [2.1] done
stage [1] done
stage [2.1] done
stage [2.2] done
stage [2.2]] done
stage [2.0] 
stage [2.3] done
stage [2.3stage [2.1] done
] done
] done
stage [2.4] done
stage [2] done
stage [2You passed!
.4] donstage [2.2e
stage [2] done
] done
stage You passed[2.3] done
!
stage [2.4] done
stage [2] done
You passed!
/testbin/triplehuge: Congratulations! You passed.
/bin/sh: subprocess time: 3.105330420 seconds
OS/161$
```

- testbin/crash

This one consists of many tests

```C
OS/161$ p /testbin/crash
[a] read from NULL
[b] read from invalid address
[c] read from kernel address
[d] write to NULL
[e] write to invalid address
[f] write to code segment
[g] write to kernel address
[h] jump to NULL
[i] jump to invalid address
[j] jump to kernel address
[k] alignment error
[l] illegal instruction
[m] divide by zero
[n] mod by zero
[o] Recurse infinitely
[*] Run everything (in subprocesses)
Note: [f] may not cause an exception on some platforms, in which
case it'll appear to fail.
Choose: Running: [a] read from NULL
Fatal user mode trap 2 sig 11 (TLB miss on load, epc 0x400310, vaddr 0x0)
Signal 11 (correct)
Running: [b] read from invalid address
Fatal user mode trap 2 sig 11 (TLB miss on load, epc 0x40032c, vaddr 0x40000000)
Signal 11 (correct)
Running: [c] read from kernel address
Fatal user mode trap 4 sig 10 (Address error on load, epc 0x400348, vaddr 0x80000000)
Signal 10 (correct)
Running: [d] write to NULL
Fatal user mode trap 3 sig 11 (TLB miss on store, epc 0x400364, vaddr 0x0)
Signal 11 (correct)
Running: [e] write to invalid address
Fatal user mode trap 3 sig 11 (TLB miss on store, epc 0x400374, vaddr 0x40000000)
Signal 11 (correct)
Running: [f] write to code segment
Fatal user mode trap 1 sig 11 (TLB modify trap, epc 0x400384, vaddr 0x40037c)
Signal 11 (correct)
Running: [g] write to kernel address
Fatal user mode trap 5 sig 10 (Address error on store, epc 0x400394, vaddr 0x80000000)
Signal 10 (correct)
Running: [h] jump to NULL
Fatal user mode trap 2 sig 11 (TLB miss on load, epc 0x4003a0, vaddr 0x0)
Signal 11 (correct)
Running: [i] jump to invalid address
Fatal user mode trap 2 sig 11 (TLB miss on load, epc 0x4003ac, vaddr 0x40000000)
Signal 11 (correct)
Running: [j] jump to kernel address
Fatal user mode trap 4 sig 10 (Address error on load, epc 0x4003b8, vaddr 0x80000000)
Signal 10 (correct)
Running: [k] alignment error
Fatal user mode trap 4 sig 10 (Address error on load, epc 0x4003f0, vaddr 0x7fffff91)
Signal 10 (correct)
Running: [l] illegal instruction
Fatal user mode trap 10 sig 4 (Illegal instruction, epc 0x4003c0, vaddr 0x0)
Signal 4 (correct)
Running: [m] divide by zero
Fatal user mode trap 9 sig 5 (Break instruction, epc 0x40042c, vaddr 0x0)
Signal 5 (correct)
Running: [n] mod by zero
Fatal user mode trap 9 sig 5 (Break instruction, epc 0x400468, vaddr 0x0)
Signal 5 (correct)
Running: [o] Recurse infinitely
Fatal user mode trap 3 sig 11 (TLB miss on store, epc 0x400484, vaddr 0x7ffefff4)
Signal 11 (correct)
/bin/sh: subprocess time: 6.316724598 seconds
OS/161$
```

- testbin/parallelvm

```C
OS/161$ p /testbin/parallelvm
Job size approximately 58800 bytes
Forking 24 jobs; total load 1378k
Process 0 (pid 65) starting computation...
Process 1 (pid 66) starting computation...
Process 2 (pid 67) starting computation...
Process 3 (pid 68) starting computation...
Process 4 (pid 69) starting computation...
Process 5 (pid 70) starting computation...
Process 4 answer 1952063315: passed
Process 7 (pid 72) starting computation...
Process 8 (pid 73) starting computation...
Process 9 (pid 74) starting computation...
Process 10 (pid 75) starting computation...
Process 11 (pid 76) starting computation...
Process 12 (pid 77) starting computation...
Process 13 (pid 78) starting computation...
Process 14 (pid 79) starting computation...
Process 15 (pid 80) starting computation...
Process 16 (pid 81) starting computation...
Process 17 (pid 82) starting computation...
Process 18 (pid 83) starting computation...
Process 17 answer 0: passed
Process 20 (pid 85) starting computation...
Process 21 (pid 86) starting computation...
Process 22 (pid 87) starting computation...
Process 23 (pid 88) starting computation...
Process 0 answer -1337312809: passed
Process 1 answer 356204544: passed
Process 2 answer -537881911: passed
Process 3 answer -65406976: passed
Process 6 (pid 71) starting computation...
Process 5 answer -843894784: passed
Process 7 answer -993925120: passed
Process 8 answer 838840559: passed
Process 9 answer -1616928768: passed
Process 10 answer -182386335: passed
Process 11 answer -364554240: passed
Process 12 answer 251084843: passed
Process 13 answer -61403136: passed
Process 14 answer 295326333: passed
Process 15 answer 1488013312: passed
Process 16 answer 1901440647: passed
Process 19 (pid 84) starting computation...
Process 18 answer -1901440647: passed
Process 20 answer -295326333: passed
Process 21 answer 61403136: passed
Process 22 answer -251084843: passed
Process 23 answer 364554240: passed
Process 6 answer 1597000869: passed
Process 19 answer -1488013312: passed
Test complete
Unknown syscall 68
Unknown syscall 68
/bin/sh: subprocess time: 12.688466258 seconds
OS/161$
```