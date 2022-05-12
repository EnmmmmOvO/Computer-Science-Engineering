"""
circle,py test
"""
from circle import Circle

def test_small():
    """
    test small value
    """
    c = Circle(3)
    assert(round(c.circumference(), 1) == 18.8)
    assert(round(c.area(), 1) == 28.3)

def test_zero():
    """
    test the value is 0
    """
    c = Circle(0)
    assert(round(c.circumference(),1) == 0)
    assert(round(c.area(),1) == 0)

def test_negative():
    """
    test the value is negative
    """
    c = Circle(-1)
    assert(round(c.circumference(),1) == 0)
    assert(round(c.area(),1) == 0)

def test_big():
    """
    test the value is large
    """
    c = Circle(100)
    assert(round(c.circumference(),1) == 628.3)
    assert(round(c.area(),1) == 31415.9)


def test_decimal():
    """
    test the value is not integer
    """
    c = Circle(0.5)
    assert(round(c.circumference(),1) == 3.1)
    assert(round(c.area(),1) == 0.8)

