import pytest
import requests
import json
from src import config

#Global safe informations
safe_email = 'iamhappy@unsw.org'
safe_password = 'abcdefg'
safe_name_first = 'Mathews'
safe_name_last = 'Andrew'

#auth_register

def test_invalid_email():
    #Email entered is not a valid email
    r = requests.post(config.url + "auth/register/v2", json={
        'email': '12345678@qq.com.au', 
        'password': safe_password, 
        'name_first': safe_name_first, 
        'name_last': safe_name_last,
    })
    assert r.status_code == 400

    r = requests.post(config.url + "auth/register/v2", json={
        'email': '12345678', 
        'password': safe_password, 
        'name_first': safe_name_first, 
        'name_last': safe_name_last,
    })
    assert r.status_code == 400

    r = requests.post(config.url + "auth/register/v2", json={
        'email': '12345678qq.com', 
        'password': safe_password, 
        'name_first': safe_name_first, 
        'name_last': safe_name_last,
    })
    assert r.status_code == 400

    r = requests.post(config.url + "auth/register/v2", json={
        'email': '', 
        'password': safe_password, 
        'name_first': safe_name_first, 
        'name_last': safe_name_last,
    })
    assert r.status_code == 400

def test_passward_too_short():
    #Password entered is less than 6 characters long
    r = requests.post(config.url + "auth/register/v2", json={
        'email': safe_email, 
        'password': '123', 
        'name_first': safe_name_first, 
        'name_last': safe_name_last,
    })
    assert r.status_code == 400

def test_invalid_first_name():
    #name_first is not between 1 and 50 characters inclusively in length
    long_name = 'watermelon' * 10
    r = requests.post(config.url + "auth/register/v2", json={
        'email': safe_email, 
        'password': safe_password, 
        'name_first': long_name, 
        'name_last': safe_name_last,
    })
    assert r.status_code == 400

    r = requests.post(config.url + "auth/register/v2", json={
        'email': safe_email, 
        'password': safe_password, 
        'name_first': '', 
        'name_last': safe_name_last,
    })
    assert r.status_code == 400

def test_invalid_last_name():
    #name_last is not between 1 and 50 characters inclusively in length
    long_name = 'watermelon' * 10
    r = requests.post(config.url + "auth/register/v2", json={
        'email': safe_email, 
        'password': safe_password, 
        'name_first': safe_name_first, 
        'name_last': long_name,
    })
    assert r.status_code == 400

    r = requests.post(config.url + "auth/register/v2", json={
        'email': safe_email, 
        'password': safe_password, 
        'name_first': safe_name_first, 
        'name_last': '',
    })
    assert r.status_code == 400

def test_auth_register():
    #Register a user successfully
    clear = requests.delete(config.url + 'clear/v1')
    assert clear.status_code == 200
    r = requests.post(config.url + "auth/register/v2", json={
        'email': safe_email, 
        'password': safe_password, 
        'name_first': safe_name_first, 
        'name_last': safe_name_last,
    })
    assert r.status_code == 200
    r = r.json()
    assert r['auth_user_id'] == 1

def test_exist_email():
    #Email address is already being used by another
    r = requests.post(config.url + "auth/register/v2", json={
        'email': safe_email, 
        'password': safe_password, 
        'name_first': safe_name_first, 
        'name_last': safe_name_last,
    })
    assert r.status_code == 400
