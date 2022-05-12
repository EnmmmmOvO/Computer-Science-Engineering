import pytest
import requests
import json
from src import config

#Global safe informations
safe_email = 'iamhappy@unsw.org'
safe_password = 'abcdefg'
safe_name_first = 'Mathews'
safe_name_last = 'Andrew'

@pytest.fixture
def setup():
    clear = requests.delete(config.url + 'clear/v1')
    assert clear.status_code == 200

    # Create User 1 - Dreams Owner
    u1_payload = requests.post(config.url + "auth/register/v2", json={
        'email': 'apple@com.au', 
        'password': 'password1', 
        'name_first': 'Steve', 
        'name_last': 'Jobs'
    })
    u1_payload = u1_payload.json()
    
    # Create User 2 - Dreams Member
    u2_payload = requests.post(config.url + "auth/register/v2", json={
        'email': 'banana@com.au', 
        'password': 'password2', 
        'name_first': 'Michael', 
        'name_last': 'Scott'
    })
    u2_payload = u2_payload.json()
    
    # Log user1 out
    requests.post(config.url + 'auth/logout/v1', json={
        'token': u1_payload['token']
    })
    
    # Log user2 out
    requests.post(config.url + 'auth/logout/v1', json={
        'token': u2_payload['token']
    })


#auth_login

def test_invalid_email():
#Email entered is not a valid email
    li = requests.post(config.url + "auth/login/v2", json={
        'email': '12345678@qq.com.au', 
        'password': safe_password, 
    })
    assert li.status_code == 400

    li = requests.post(config.url + "auth/login/v2", json={
        'email': '12345678', 
        'password': safe_password, 
    })
    assert li.status_code == 400

    li = requests.post(config.url + "auth/login/v2", json={
        'email': '12345678qq.com', 
        'password': safe_password, 
    })
    assert li.status_code == 400

    li = requests.post(config.url + "auth/login/v2", json={
        'email': '', 
        'password': safe_password, 
    })
    assert li.status_code == 400

def test_no_user_email(setup):
#Email entered does not belong to a user
    li = requests.post(config.url + 'auth/login/v2', json={
        'email': 'nouseremail@qq.com', 
        'password': safe_password,
    })
    assert li.status_code == 400

def test_incorrect_password():
#Password is not correct
    li = requests.post(config.url + 'auth/login/v2', json={
        'email': 'apple@com.au', 
        'password': 'wrongpassword',
    })
    assert li.status_code == 400

def test_login(setup):
#Login users
    li1 = requests.post(config.url + "auth/login/v2", json={
        'email': 'apple@com.au', 
        'password': 'password1', 
    })
    assert li1
    assert li1.status_code == 200

    li2 = requests.post(config.url + "auth/login/v2", json={
        'email': 'banana@com.au', 
        'password': 'password2', 
    })
    assert li2.status_code == 200
    
    li1_again =requests.post(config.url + "auth/login/v2", json={
        'email': 'apple@com.au', 
        'password': 'password1', 
    })
    assert li1_again.status_code == 200
