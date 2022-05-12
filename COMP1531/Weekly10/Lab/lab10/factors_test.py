from factors import factors, is_prime
from hypothesis import given, strategies
import inspect

def test_generator():
    '''
    Ensure it is generator function
    '''
    assert inspect.isgeneratorfunction(factors), "factors does not appear to be a generator"


