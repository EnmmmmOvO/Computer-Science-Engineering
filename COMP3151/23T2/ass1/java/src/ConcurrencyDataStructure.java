import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.Semaphore;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.locks.ReentrantReadWriteLock;


public class ConcurrencyDataStructure {
    private final List<Integer> list;
    private final int N;
    private final List<ReentrantReadWriteLock> lock;
    private final Semaphore total;
    private AtomicInteger cleanup = new AtomicInteger(0);

    public ConcurrencyDataStructure(int n) {
        N = n;
        list = new ArrayList<>(Collections.nCopies(n, -1));
        lock = new ArrayList<>(Collections.nCopies(n, new ReentrantReadWriteLock(false)));
        total = new Semaphore(n);
    }

    public void insert(int n) {
        total.acquireUninterruptibly();
        int i = 0;

        while (i < N) {
            lock.get(i).writeLock().lock();
            if (list.get(i) == -1) {
                int j = i + 1;

                if (j == N) {
                    list.set(i, n);
                    lock.get(i).writeLock().unlock();
                    break;
                }

                while (j < N) {
                    lock.get(j).writeLock().lock();

                    if (list.get(j) == -1) j++;
                    else if (list.get(j) < n) {
                        list.set(i, list.get(j));
                        list.set(j, -1);
                        lock.get(i).writeLock().unlock();
                        i++;
                        j++;
                        continue;
                    } else if (list.get(j) == n) {
                        for (; j >= i; j--) lock.get(j).writeLock().unlock();
                        total.release();
                        i = N;
                        break;
                    }

                    if (j == N || list.get(j) > n) {
                        list.set(i, n);
                        if (j == N) j--;
                        for (; j >= i; j--) lock.get(j).writeLock().unlock();
                        i = N;
                        break;
                    }
                }
            } else if (list.get(i) < n) {
                lock.get(i).writeLock().unlock();
                i++;
            } else if (list.get(i) > n) {
                int j = i + 1;
                while (true) {
                    lock.get(j).writeLock().lock();
                    if (list.get(j) == -1) {
                        for (; j > i; j--) {
                            list.set(j, list.get(j - 1));
                            lock.get(j).writeLock().unlock();
                        }
                        list.set(i, n);
                        lock.get(i).writeLock().unlock();
                        i = N;
                        break;
                    } else j++;
                }
            } else {
                System.out.println("number exists");
                lock.get(i).writeLock().unlock();
                total.release();
                break;
            }
        }

    }

    public void delete1(int n) {
        int low = 0;
        int high = N - 1;

        while (low <= high) {
            int mid = low + (high - low) / 2;
            lock.get(mid).writeLock().lock();

            if (list.get(mid) == -1) {
                // The current position is empty, need to find the nearest non-empty position
                int left = mid - 1;
                int right = mid + 1;

                while (true) {
                    if (left >= low) {
                        lock.get(left).writeLock().lock();
                        if (list.get(left) != -1) {
                            lock.get(mid).writeLock().unlock();
                            mid = left;
                            break;
                        }
                        lock.get(left).writeLock().unlock();
                        left--;
                    }
                    if (right <= high) {
                        lock.get(right).writeLock().lock();
                        if (list.get(right) != -1) {
                            lock.get(mid).writeLock().unlock();
                            mid = right;
                            break;
                        }
                        lock.get(right).writeLock().unlock();
                        right++;
                    }
                    if (left < low && right > high) {
                        // All the remaining positions are empty
                        System.out.println("number not found");
                        return;
                    }
                }
            }

            if (list.get(mid) == n) {
                list.set(mid, -1);
                lock.get(mid).writeLock().unlock();
                total.release();
                int cleanupCount = cleanup.incrementAndGet();
                if (cleanupCount >= N / 2) {
                    cleanup.set(0);
                    new Thread(() -> {
                        insert(Integer.MAX_VALUE);
                        delete(Integer.MAX_VALUE);
                    }).start();
                }
                return;
            } else if (list.get(mid) > n) {
                lock.get(mid).writeLock().unlock();
                high = mid - 1;

                // Try to move left to find the number
                int left = mid - 1;
                while (left >= low) {
                    lock.get(left).writeLock().lock();
                    if (list.get(left) == -1 || list.get(left) < n) {
                        lock.get(left).writeLock().unlock();
                        break;
                    } else if (list.get(left) == n) {
                        list.set(left, -1);
                        lock.get(left).writeLock().unlock();
                        total.release();
                        int cleanupCount = cleanup.incrementAndGet();
                        if (cleanupCount >= N / 2) {
                            cleanup.set(0);
                            new Thread(() -> {
                                insert(Integer.MAX_VALUE);
                                delete(Integer.MAX_VALUE);
                            }).start();
                        }
                        return;
                    }
                    lock.get(left).writeLock().unlock();
                    left--;
                }
            } else {
                lock.get(mid).writeLock().unlock();
                low = mid + 1;

                // Try to move right to find the number
                int right = mid + 1;
                while (right <= high) {
                    lock.get(right).writeLock().lock();
                    if (list.get(right) == -1 || list.get(right) > n) {
                        lock.get(right).writeLock().unlock();
                        break;
                    } else if (list.get(right) == n) {
                        list.set(right, -1);
                        lock.get(right).writeLock().unlock();
                        total.release();
                        int cleanupCount = cleanup.incrementAndGet();
                        if (cleanupCount >= N / 2) {
                            cleanup.set(0);
                            new Thread(() -> {
                                insert(Integer.MAX_VALUE);
                                delete(Integer.MAX_VALUE);
                            }).start();
                        }
                        return;
                    }
                    lock.get(right).writeLock().unlock();
                    right++;
                }
            }
        }

        System.out.println("number not found");
    }

    public void delete(int n) {
        int low = 0;
        int high = N - 1;
        boolean find = false;

        while (low <= high) {
            int mid = low + (high - low) / 2;
            lock.get(mid).writeLock().lock();

            try {
                if (list.get(mid) == -1) {
                    // The current position is empty, need to find the nearest non-empty position
                    int temp = mid;
                    boolean found = false;

                    // Check left
                    while (--temp >= low) {
                        lock.get(mid).writeLock().unlock();
                        lock.get(temp).writeLock().lock();
                        mid = temp;
                        if (list.get(mid) != -1) {
                            found = true;
                            break;
                        }
                    }

                    // If no valid position found on the left, update 'low' and continue the next iteration
                    if (!found) {
                        low = mid + 1;
                        continue;
                    }
                }

                if (list.get(mid) == n) {
                    list.set(mid, -1);
                    total.release();
                    find = true;
                    break;
                } else if (list.get(mid) < n) {
                    low = mid + 1;
                } else {
                    high = mid - 1;
                }
            } finally {
                lock.get(mid).writeLock().unlock();
            }
        }

        if (find) {
            int cleanupCount = cleanup.incrementAndGet();
            if (cleanupCount >= N / 2) {
                cleanup.set(0);
                new Thread(() -> {
                    insert(Integer.MAX_VALUE);
                    delete(Integer.MAX_VALUE);
                }).start();
            }
        } else System.out.println("number not found");
    }


    public boolean member(int n) {
        int low = 0;
        int high = N - 1;

        while (low <= high) {
            int mid = low + (high - low) / 2;
            lock.get(mid).readLock().lock();

            try {
                if (list.get(mid) == -1) {
                    int temp = mid;
                    boolean found = false;

                    while (--temp >= low) {
                        lock.get(mid).readLock().unlock();
                        lock.get(temp).readLock().lock();
                        mid = temp;
                        if (list.get(mid) != -1) {
                            found = true;
                            break;
                        }
                    }

                    if (!found) {
                        low = mid + 1;
                        continue;
                    }
                }

                if (list.get(mid) == n) {
                    return true;
                } else if (list.get(mid) < n) {
                    low = mid + 1;
                } else {
                    high = mid - 1;
                }
            } finally {
                lock.get(mid).readLock().unlock();
            }
        }

        return false;
    }

    public void print_sort() {
        System.out.print("[ ");
        for (int i = 0; i < N; i++) {
            lock.get(i).readLock().lock();
            if (list.get(i) != -1) System.out.print(list.get(i) + " ");
            lock.get(i).readLock().unlock();
        }
        System.out.println("]");
    }
}
