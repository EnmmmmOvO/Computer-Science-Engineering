'''
Tests for reverse_words()
'''
from reverse import reverse_words

def test_example_1():
    assert reverse_words(["Hello World", "I am here"]) == ['World Hello', 'here am I']

def test_example_2():
    assert reverse_words(["Hello World"]) == ['World Hello']

def test_example_3():
    assert reverse_words([]) == []

def test_example_4():
    assert reverse_words(["Hello World", "I am here", "COMP1531"]) == ['World Hello', 'here am I', 'COMP1531']

def test_example_5():
    assert reverse_words(["Hello World", "I am here", "COMP1531", "I am a global student"]) == ['World Hello', 'here am I', 'COMP1531', 'student global a am I']

def test_example_6():
    assert reverse_words(["Hello World", "I am here", "COMP1531", "I am a global student", "aLL Right"]) == ['World Hello', 'here am I', 'COMP1531', 'student global a am I', 'Right aLL']

