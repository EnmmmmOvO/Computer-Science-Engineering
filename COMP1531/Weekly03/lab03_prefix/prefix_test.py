from prefix import prefix_search
import pytest

def test_documentation_a():
    assert prefix_search({"ac": 1, "ba": 2, "ab": 3}, "a") == { "ac": 1, "ab": 3}

def test_documentation_b():
    assert prefix_search({"ab": 1, "abc": 2, "abcd": 3}, "a") == { "ab": 1, "abc": 2, "abcd": 3}

def test_documentation_c():
    assert prefix_search({}, "a") == {}

def test_documentation_b():
    assert prefix_search({"bx": 1}, "a") == {}

def test_exact_match_a():
    assert prefix_search({"category": "math", "cat": "animal"}, "cat") == {"category": "math", "cat": "animal"}

def test_exact_match_b():
    assert prefix_search({"category": "math", "cat": "animal", "tca": "good"}, "cat") == {"category": "math", "cat": "animal"}

