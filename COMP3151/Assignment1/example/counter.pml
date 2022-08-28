// counter.pml
// Authors: Michael Cunanan (z5204816), Kenvin Yu (z5207857)

// Results:
//  Attempted to verify no deadlock: max depth reached
//  Attempted to verify eventaul completion of reads: max depth reached

// Terminology:
//  Carry-over: When adding 1 to the current digit causes this digit to be set to 0, and to incrememnt the next byte.
//  Overflow: When the most signficant bit has carry-over, and the whole counter is set to 0.

#define B 2
#define R 2
#define MAX 5 // Normally the MAX value for a byte is 255, but we artificially lower it for verficiation 

//  Two copies of our counter. At the end of every 'write', these will be equal.
//  Counters have the most signficant byte on the left (and least significant on the right)
//  (Left means lowest index)
byte c[B];
byte d[B];

//  Two copies of a 'parity' bit. These will be used to determine overflow.
bit p1 = 0;
bit p2 = 0;

//  Ghost variables which are only used for verification purposes.
//  If we remove all code involving ghost variables, we end up with a normal solution.
//  Most are arrays and they are meant to reflect what each reader sees.
byte    ghost_C[B*R];
byte    ghost_D[B*R];
byte    ghost_V[B*R];
bool    ghost_overflow[R];
bool    ghost_overflow_after[R];
bool    ghost_will_signal;
bit     ghost_q1[R];
bit     ghost_q2[R];


active proctype Writer() {
    byte e[B];  // Private temporary buffer to write/read from.
    int i;      // Counter variable.
    byte q;     // Private temporary byte to read in parity bits.
    
    do
    ::
        ghost_will_signal = false;  // Indicate whether or not to signal overflow for later.
        q = p1;                     // Read in the parity bit p1.
        for (i : 0..(B-1)) {        // Read c into e. Because we are the only on editing c (and d), the direction of this read doesn't matter.
            e[i] = c[i];
        }
        // This loop has the logic for adding 1 to e, and detecting overflow.
        i = B-1;                    // Promela doesn't have backwards ranges, so we have this instead.
        do
        ::  (i >= 0) ->
            if
            ::  (e[i] == MAX) ->    // If the current digit is the maximum, we have carry-over
                if
                ::  (i == 0) ->     // If the most signficant bit has carry-over, we indicate overflow.
                    atomic {
                        q = 1 - q;  // Change the local parity bit.
                        ghost_will_signal = true;   // Indicate that we should signal overflow.
                    }
                ::  else -> skip;
                fi;
                e[i] = 0;
            ::  else ->
                e[i]++; // Add 1 to current digit
                break;  // Because this doesn't overflow, we are done adding.
            fi
            i--;
        ::  else -> break;
        od;
        
        // In our implementation, we declare the start of a write to happen at the start of an access to shared memory.
        // In this case, we access p2 first.
        // Simulatenously, we indicate on the ghost variables that the counter has overflowed.
        atomic {
            if
            ::  ghost_will_signal -> 
                for (i: 0..(R-1)) {
                    ghost_overflow[i] = true;
                }
            ::  else -> skip;
            fi;
            p2 = q;
        }

        // Copy e in d, left to right.
        for (i : 0..(B-1)) {
            d[i] = e[i];
        }
        // Copy e in c, right to left.
        for (i : 0..(B-1)) {
            c[B-1-i] = e[B-1-i];
        }

        p1 = q; // Save the parity bit into p1.
        // We have now completed a `write'.
    od
}

active[R] proctype Reader() {
    byte s[B];  // Private buffer to read from c.
    byte t[B];  // Private buffer to read from d.
    byte v[B];  // Private buffer to store the 'read' result (not necessarily equal to c or d).

    bit q1;     // Private variable to read in parity bit p1.
    bit q2;     // Private variable to read in parity bit p2.

    int i;

    do 
    ::  skip;   
en:     skip;   // Label for eventual entry.

        // Reset the result to all 0's.
        for (i : 0..(B-1)) {
            v[i] = 0;
        }
  
        // In our implementation, the 'start' of a 'read' occurs at the first access of shared memory.
        // In this case we access p1 first.
        // Simultaeneously, we 'remember' whether overflow has happened or not on the ghost variables.
        // We also save the value of q1 and C for later verification.
        atomic {
            q1 = p1;
            ghost_overflow_after[_pid-1] = ghost_overflow[_pid-1];
            ghost_q1[_pid-1] = q1;
            ghost_overflow[_pid-1] = ghost_q1[_pid-1] != ghost_q2[_pid-1];
            for (i : 0..(B-1)) {
                ghost_C[B*(_pid-1)+i] = c[i];
            }
        }

        // Note that the order of the next two loops matter, since we (readers) are not in control of c or d.
        // Read from c into s, left to right.
        for (i : 0..(B-1)) {
            s[i] = c[i];
        }
        
        // Read from d into t, right to left.
        for (i : 0..(B-1)) {
            t[B - 1 - i] = d[B - 1 - i];
        }

        // The 'read' ends on the last access of shared memory.
        // In this case, the last access is to p2.
        // Simulatenously, we save the value of q2 and D for later verfication.
        // We also check whether the value of 'ghost_overflow_after' has changed since we set it.
        atomic {
            q2 = p2;
            ghost_q2[_pid-1] = q2;
            ghost_overflow_after[_pid-1] = ghost_overflow[_pid-1] || ghost_overflow_after[_pid-1];
            for (i : 0..(B-1)) {
                ghost_D[B*(_pid-1)+i] = d[i];
            }
        }

        // After reading in the values from c and d, we have to do some post-processing before we declare what value we read.
        if 
        ::  q1 != q2 -> skip;   // If the parity bits are different, then we can just stick with an answer of all 0's.
        ::  else ->             // More details on the else case in the proof.
            i = 0; 
            do 
            ::  i < B && s[i] == t[i] ->    // Any commonalities are saved to the answer.
                v[i] = t[i]; 
                i++;
            ::  else -> break;
            od;
            if 
            ::  i != B -> v[i] = t[i];  // Any bytes past the first difference get left as 0.
            ::  else ->skip; 
            fi;
            
        fi;
        //  Save the value of the answer 'v' to a ghost variable.
        atomic {
            for (i: 0..(B-1)) {
                ghost_V[B*(_pid-1)+i] = v[i];
            }
        }
red:    skip; // At this point v is the read-in value 
    od;
}

// Eventual completion checks. (Liveness property)
// WARNING: Needs to be adjusted when R changes
#define reads_complete_a ( always (Reader[0]@en -> eventually Reader[0]@red) )
#define reads_complete_b ( always (Reader[1]@en -> eventually Reader[1]@red) )
ltl reads_complete { reads_complete_a && reads_complete_b }


// Macro to check if one counter is less than or equal to another.
// WARNING: Needs to be adjusted when B changes 
#define LEQ(x,y,p) (x[B*p+0]<y[B*p+0] || (x[B*p+0]==y[B*p+0] && x[B*p+1]<=y[B*p+1]))
// Functional correctness checks. (Safety properties)
//  Overflow: Once we are done with a 'read', make sure we can reliably use q1 and q2 to infer overflow.
//  Func_correct: Once we are done with a 'read', make sure we have C <= V <= D. (explained in proof).
// WARNING: Needs to be adjusted when R changes
ltl overflow_a { always ((Reader[1]@red && ghost_q1[0] != ghost_q2[0]) -> ghost_overflow_after[0]) }
ltl func_correct_a { always (Reader[1]@red -> (!ghost_overflow_after[0] -> (LEQ(ghost_C,ghost_V,0) && LEQ(ghost_V,ghost_D,0))))}

ltl overflow_b { always ((Reader[2]@red && ghost_q1[1] != ghost_q2[1]) -> ghost_overflow_after[1]) }
ltl func_correct_b { always (Reader[2]@red -> (!ghost_overflow_after[1] -> (LEQ(ghost_C,ghost_V,1) && LEQ(ghost_V,ghost_D,1))))}
