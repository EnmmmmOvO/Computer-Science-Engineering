'''
Tests for check_password()
'''
import password


def test_a():
    assert password.check_password("123456") == "Horrible password"

def test_b():
    assert password.check_password("iloveyou") == "Horrible password"

def test_c():
    assert password.check_password("password") == "Horrible password"

def test_d():
    assert password.check_password("Abcdefjhijklmn1234567890") == "Strong password"

def test_e():
    assert password.check_password("Abcdefjhijq0") == "Strong password"

def test_F():
    assert password.check_password("Abcdefjhi0") == "Moderate password"

def test_G():
    assert password.check_password("Abcdefjhieeeeee") == "Poor password"

def test_h():
    assert password.check_password("bcsssssssssssssssssdefjhi0") == "Moderate password"

def test_i():
    assert password.check_password("AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA0") == "Moderate password"

def test_j():
    assert password.check_password("AbcdefjhiQWERQWERQWRQWE") == "Poor password"

def test_k():
    assert password.check_password("Abcde") == "Poor password"
