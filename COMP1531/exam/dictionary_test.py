'''
dictionary test
'''
from dictionary import construct_dict


def test_1():
    '''
    test1
    '''
    l1 = ['a', 'b', 'c']
    l2 = [1, 2, 3]
    assert (construct_dict(l1, l2) == {'a': 1, 'b': 2, 'c': 3})


def test_2():
    '''
    test2
    '''
    l1 = ['a', 'b', 'b']
    l2 = [1, 2, 3]
    assert (construct_dict(l1, l2) == {'a': 1, 'b': 3})


def test_3():
    '''
    test3
    '''
    l1 = ['a', 'b', 'b']
    l2 = [1, 2]
    try:
        construct_dict(l1, l2)
    except Exception as e:
        assert isinstance(e, ValueError)
