'''
arconym test
'''

from acronym import acronym_make


def test_1():
    '''
    test1
    '''
    assert acronym_make(['I am very tired today']) == ['VTT']


def test_2():
    '''
    test2
    '''
    assert acronym_make(['Why didnt I study for this exam more', 'I dont know']) == ['WDSFTM', 'DK']


def test_3():
    '''
    test3
    '''
    try:
        acronym_make([])
    except Exception as e:
        assert isinstance(e, ValueError)


def test_4():
    '''
    test4
    '''
    assert acronym_make(["A A A A A A A A A A A A"]) == ["N/A"]
