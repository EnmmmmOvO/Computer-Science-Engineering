'''
encapsulate.py pytest
'''
from encapsulate import Student
from datetime import datetime
from pytest import fixture

@fixture
def student():
    '''
    define the name and the birthday
    '''
    return Student('Rob', 'Everest', 1961)

def test_name(student):
    '''
    pytest name
    '''
    assert student.getName() == 'Rob Everest'

def test_age(student):
    '''
    pytest birthday
    ''' 
    assert student.getAge() == datetime.now().year - 1961
