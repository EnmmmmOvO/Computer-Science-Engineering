'''
distance test
'''

from distance import longest_distance


def test_1():
    '''
    test1
    '''
    assert (longest_distance([1, 2, 3, 1, 4]) == 3)


def test_2():
    '''
    test2
    '''
    assert (longest_distance([1, 2, 3, 4, 5]) == 0)


def test_3():
    '''
    test3
    '''
    assert (longest_distance([1, 2, 3, 1, 2]) == 3)


def test_4():
    '''
    test4
    '''
    assert (longest_distance([1, 2, 3, 2, 1]) == 4)


def test_5():
    '''
    test5
    '''
    assert (longest_distance([2, 1, 2, 3, 1]) == 3)
