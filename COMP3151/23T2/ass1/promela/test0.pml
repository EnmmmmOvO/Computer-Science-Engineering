// Test insert() and insert()

# define N 3

int array[N];
int lock[N];
int total = N;

inline read_lock(n) {
    atomic { lock[n] >= 0 ; lock[n] = lock[n] + 1 }
} 

inline write_lock(n) {
    atomic { lock[n] == 0; lock[n] = -1 }
}

inline read_unlock(n) {
    atomic { lock[n] = lock[n] - 1; }
}

inline write_unlock(n) {
    atomic { lock[n] = 0; }
}

inline release(s) { 
    s++; 
}
inline acquire(s)  {
    atomic{
        s > 0; s--;
    }
}

proctype init_structure() {
    byte i;
    for (i : 0 .. N - 1) {
        lock[i] = 0;
        array[i] = -1;
    }
}

proctype insert(byte n) {
    acquire(total);
    int i = 0
    int j;

    do
    :: i >= N -> break
    :: else ->
        write_lock(i);
        if 
        :: array[i] == -1 -> 
            j = i + 1;
            if
            :: j == N ->
                array[i] = n;
                write_unlock(i);
                i = N;
                break
            :: else -> skip
            fi

            do
            :: j >= N -> break;
            :: else ->
                write_lock(j);
                if
                :: array[j] == -1 -> j = j + 1
                :: else -> skip;
                fi

                if
                :: j == N ->
                    array[i] = n;
                    j = j - 1;
                    do
                    :: j >= i ->
                        write_unlock(j);
                        j = j - 1;
                    :: else -> break;
                    od
                    i = N;
                    break
                :: else -> skip;
                fi


                if
                :: array[j] != -1 && array[j] < n ->
                    array[i] = array[j];
                    array[j] = -1;
                    write_unlock(i);
                    i = i + 1;
                    j = j + 1;
                :: array[j] != -1 && array[j] == n ->
                    do
                    :: j >= i ->
                        write_unlock(j);
                        j = j - 1;
                    :: else -> break;
                    od
                    release(total);
                    i = n
                    break
                :: array[j] != -1 && array[j] > n ->
                    array[i] = n;
                    do
                    :: j >= i ->
                        write_unlock(j);
                        j = j - 1;
                    :: else -> break;
                    od
                    i = N;
                    break
                :: else -> skip
                fi
            od   
        :: array[i] != -1 && array[i] < n -> 
            write_unlock(i);
            i = i + 1
        :: array[i] > n ->  
            j = i + 1;
            do
            :: true ->
                write_lock(j);

                if 
                :: array[j] == -1 ->
                    do
                    :: j > i ->
                        array[j] = array[j - 1];
                        write_unlock(j);
                        j = j - 1;
                    :: else -> break
                    od
                    array[i] = n;
                    write_unlock(i);
                    i = N;
                    break
                :: else -> j = j + 1
                fi
            od
        :: else -> 
            write_unlock(i);
            i = N;
            release(total);
            break
        fi
    od
}

proctype delete(byte n) {
    int low = 0;
    int high = N - 1;
    int mid;
    start:
    do  
    :: low <= high -> 
        mid = low + (high - low) / 2;
        write_lock(mid);

        if 
        :: array[mid] == -1 ->
            int temp = mid;
            bool found = false;

            temp--;
            do
            :: temp >= low ->
                write_unlock(mid);
                write_lock(temp);
                mid = temp;
                if 
                :: array[mid] != -1 ->
                    found = true;
                    break
                :: else -> skip
                fi
                temp--;
            :: else -> break
            od

            if 
            :: !found -> 
                write_unlock(mid);
                low = mid + 1;
                goto start;
            :: else -> skip
            fi
        :: else -> skip
        fi

        if 
        :: array[mid] == n ->
            array[mid] = -1;
            release(total);
            write_unlock(mid);
            break
        :: array[mid] < n -> low = mid + 1;
        :: else -> high = mid - 1;
        fi
        write_unlock(mid);
    :: else -> break
    od
    end:
}

proctype delete1(byte n) {
    int low = 0;
    int high = N - 1;
    int left;
    int right;

    do
    :: low <= high ->
        int mid = low + (high - low) / 2;
        write_lock(mid);

        if 
        :: array[mid] == -1 -> 
            left = mid - 1;
            right = mid + 1;

            do
            :: true -> 
                if 
                :: left >= low ->
                    write_lock(left);

                    if 
                    :: array[left] != -1 ->
                        write_unlock(mid);
                        mid = left
                        break;
                    :: else -> skip
                    fi

                    write_unlock(left);
                    left--;
                :: else -> skip;
                fi

                if
                :: right <= high ->
                    write_lock(right);
                    if
                    :: array[right] != -1 ->
                        write_unlock(mid);
                        mid = right;
                        break;
                    :: else -> skip
                    fi
                    write_unlock(right)
                    right++;
                :: else -> skip
                fi

                if
                :: left < low && right > high -> goto end;
                :: else -> skip
                fi
            od
        :: else -> skip
        fi

        if 
        :: array[mid] == n ->
            array[mid] = -1;
            write_unlock(mid);
            release(total)
            goto end;
        :: array[mid] > 0 ->
            write_unlock(mid);
            high = mid - 1;
            left = mid - 1;
            do
            :: left >= low ->
                write_lock(left);
                if
                :: array[left] == -1 ->
                    write_unlock(left);
                    break;
                :: array[left] < n ->
                    write_unlock(left);
                    break;
                :: array[left] == n ->
                    array[left] = -1;
                    write_unlock(left);
                    release(total)
                    goto end;
                :: else -> skip
                fi
            :: else -> break
            od
        :: else ->
            write_unlock(mid);
            low = mid - 1;
            right = mid + 1;
            do
            :: right <= high ->
                write_unlock(right);
                if
                :: array[right] == -1 ->
                    write_unlock(right);
                    break;
                :: array[right] > n ->
                    write_unlock(right);
                    break;
                :: array[right] == n ->
                    array[right] = -1;
                    write_unlock(right);
                    release(total)
                    goto end;
                :: else -> skip
                fi
                write_unlock(right);
                right++;
            :: else -> break
            od
        fi
    :: else -> break;
    od
    end:
}

proctype member(byte n) {
    int low = 0;
    int high = N - 1;
    int mid;
    int find = false;
    start:
    do  
    :: low <= high -> 
        mid = low + (high - low) / 2;
        read_lock(mid);

        if 
        :: array[mid] == -1 ->
            int temp = mid;
            bool found = false;

            temp--;
            do
            :: temp >= low ->
                read_unlock(mid);
                read_lock(temp);
                mid = temp;
                if 
                :: array[mid] != -1 ->
                    found = true;
                    break
                :: else -> skip
                fi
                temp--;
            :: else -> break
            od

            if 
            :: !found -> 
                read_unlock(mid);
                low = mid + 1;
                goto start;
            :: else -> skip
            fi
        :: else -> skip
        fi

        if 
        :: array[mid] == n ->
            find = true;
            break
        :: array[mid] < n -> low = mid + 1;
        :: else -> high = mid - 1;
        fi
        read_unlock(mid);
    :: else -> break
    od
    
    if
    :: find -> printf("find");
    :: else -> printf("not find");
    fi
}

proctype print_sorted() {
    byte i;
    for (i: 0 .. N - 1) {
        read_lock(i);
        printf("%d ", array[i]);
        read_unlock(i);
    }

}

init {
    run init_structure();
    _nr_pr == 1;

    run insert(0);
    run insert(1);
    run insert(2);

    assert(array[0] < array[1]);
    assert(array[1] < array[2]);
    assert(array[2] < array[3]);
    assert(lock[0] == 0);
    assert(lock[1] == 0);
    assert(lock[2] == 0);
    assert(total == 0);
}
