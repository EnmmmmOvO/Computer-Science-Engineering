'''
NOTE: This exercise assumes you have completed divisors.py
'''

from divisors import divisors

# You may find this helpful
def is_prime(n):
    return n != 1 and divisors(n) == {1, n}

def factors(n):
    '''
    A generator that generates the prime factors of n. For example
    >>> list(factors(12))
    [2,2,3]

    Params:
      n (int): The operand

    Yields:
      (int): All the prime factors of n in ascending order.

    Raises:
      ValueError: When n is <= 1.
    '''
    
    for i in range(2, n):
    while n % i == 0:
        yield i
        n //= i
