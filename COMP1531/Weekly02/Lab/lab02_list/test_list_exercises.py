from list_exercises import *

def test_reverse_a():
    l = ["how", "are", "you"]
    l = reverse_list(l)
    assert l == ['you', 'are', 'how']

def test_reverse_b():
    l = ["Python", "C", "C++", "Java", "C#"]
    l = reverse_list(l)
    assert l == ['C#', 'Java', 'C++', 'C', 'Python']

def test_reverse_c():
    l = [" ", ".", " ", ".", " ", "|"]
    l = reverse_list(l)
    assert l == ['|', ' ', '.', ' ', '.', ' ']

def test_min_positive_a():
    assert minimum([1, 2, 3, 10]) == 1

def test_min_positive_b():
    assert minimum([33, 52, 13, 64, 1000000]) == 13

def test_min_positive_c():
    assert minimum([-100000000000000000, -111111111111111, 10000000000000000, 100000000000000000]) == -100000000000000000

def test_sum_positive_a():
    assert sum_list([7, 7, 7]) == 21

def test_sum_positive_b():
    assert sum_list([7, 8, 9]) == 24

def test_sum_positive_c():
    assert sum_list([1, 2, 3, 4, 5, 6, 7, 8, 9, 10]) == 55  