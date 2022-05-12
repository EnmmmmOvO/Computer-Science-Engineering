from divisors import divisors
from hypothesis import given, strategies

def test_12():
    assert divisors(12) == {1,2,3,4,6,12}
