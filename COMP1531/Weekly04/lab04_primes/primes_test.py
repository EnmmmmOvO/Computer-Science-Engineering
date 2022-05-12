"""
prime test
"""
import primes

def test_a():
    """
    number is primes
    """
    assert(primes.factors(11) == [11])
    assert(primes.factors(3) == [3])
    assert(primes.factors(5) == [5])


def test_b():
    """
    number is negative
    """
    assert(primes.factors(-1) == False)
    assert(primes.factors(-8) == False)
    assert(primes.factors(-3) == False)

def test_c():
    """
    number is 0
    """
    assert(primes.factors(0) == False)

def test_d():
    """
    number is 1
    """
    assert(primes.factors(1) == False)

def test_e():
    """
    test number
    """
    assert(primes.factors(112) == [2, 2, 2, 2, 7])
    assert(primes.factors(1024) == [2, 2, 2, 2, 2, 2, 2, 2, 2, 2])
    assert(primes.factors(8) == [2, 2, 2])
    assert(primes.factors(27) == [3, 3, 3])
    assert(primes.factors(21) == [3, 7])

def test_f():
    """
    test number
    """
    assert(primes.factors(112.1) == False)
    assert(primes.factors(0.1) == False)
    assert(primes.factors(-112.1) == False)





