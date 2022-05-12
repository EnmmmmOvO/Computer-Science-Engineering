def divisors(n):
    '''
    Given some number n, return a set of all the numbers that divide it. For example:
    >>> divisors(12)
    {1, 2, 3, 4, 6, 12}

    Params:
      n (int): The operand

    Returns:
      (set of int): All the divisors of n

    Raises:
      ValueError: If n is not a positive integer
    '''

    if n <= 0:
        return ValueError
    elif n == 1:
        return 1
    else:
        divisor = {}
        for i in range (1, n+1):
            if n % i == 0:
                i.divisor()
        return divisor

if __name__ == '__main__':
    print(divisors(12))

        