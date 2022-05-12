from inverse import inverse
#from hypothesis import given, strategies


def test():
    assert inverse({}) == {}
    assert inverse({1: 'A', 2: 'B', 3: 'A'}) == {'A': [1, 3], 'B': [2]}
    

