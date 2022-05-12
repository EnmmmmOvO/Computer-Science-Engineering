"""
stack_test
"""
from stack import Stack

def test_a():
    """
    test word python and pytest
    """
    stack_obj = Stack()
    stack_obj.push("python")
    assert(stack_obj.pop() == "python")

    stack_obj = Stack()
    stack_obj.push("pytest")
    assert(stack_obj.pop() == "pytest")

def test_b():
    """
    test number
    """
    stack_obj = Stack()
    stack_obj.push("0")
    assert(stack_obj.pop() == "0")

def test_c():
    """
    test False situation
    """
    stack_obj = Stack()
    stack_obj.push(False)
    assert(stack_obj.pop() == False)

def test_d():
    """
    test display siutation
    """
    stack_obj = Stack()
    stack_obj.push('python')
    assert(stack_obj.display() == None)

