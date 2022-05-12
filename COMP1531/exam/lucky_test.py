'''
lucky test
'''

from lucky import lucky


def test_1():
    '''
    test 1
    '''
    assert lucky(1, 19, 4) == [1, 3, 7, 9, 13, 15]


def test_2():
    '''
    test 2
    '''
    assert lucky(2, 10, 6) == [2, 4, 6, 10]


def test_3():
    '''
    test 3
    '''
    assert lucky(1, 1, 5) == [1]
