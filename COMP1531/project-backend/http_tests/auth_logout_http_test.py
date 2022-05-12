import pytest
import requests
import json
from src import config

#Global safe informations
safe_email = 'iamhappy@unsw.org'
safe_password = 'abcdefg'
safe_name_first = 'Mathews'
safe_name_last = 'Andrew'
invalid_token = 'today is Friday'

#an invalid token
invalid_token = 'eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJzZXNzaW9uc19pZCI6MX0.VRz789P4O1iWpmqlZupD25REjznk5kB1ICLnPnQaTdI'

@pytest.fixture
def setup():
    clear = requests.delete(config.url + 'clear/v1')
    assert clear.status_code == 200

    # Create User 1
    u1_payload = requests.post(config.url + "auth/register/v2", json={
        'email': 'apple@com.au', 
        'password': 'password1', 
        'name_first': 'Steve', 
        'name_last': 'Jobs'
    })
    u1_payload = u1_payload.json()
    
    # Create User 2
    u2_payload = requests.post(config.url + "auth/register/v2", json={
        'email': 'banana@com.au', 
        'password': 'password2', 
        'name_first': 'Michael', 
        'name_last': 'Scott'
    })
    u2_payload = u2_payload.json()
    
    # Create second User 1
    u1_second_payload = requests.post(config.url + "auth/login/v2", json={
        'email': 'apple@com.au', 
        'password': 'password1', 
    })
    u1_second_payload = u1_second_payload.json()
    return {
        'user1' : u1_payload,
        'user2' : u2_payload,
        'user_second_1' : u1_second_payload,
    }

def test_invalid_token():
#Token passed is a invalid id
    clear = requests.delete(config.url + 'clear/v1')
    assert clear.status_code == 200
    
    lo = requests.post(config.url + 'auth/logout/v1', json={
        'token': invalid_token,
    })
    assert lo.status_code == 403

def test_logout(setup):
#Logout users
    lo = requests.post(config.url + 'auth/logout/v1', json={
        'token': setup['user1']['token'],
    })
    assert lo.status_code == 200
    lo = lo.json()
    assert lo['is_success'] == True

    lo = requests.post(config.url + 'auth/logout/v1', json={
        'token': setup['user_second_1']['token'],
    })
    assert lo.status_code == 200
    lo = lo.json()
    assert lo['is_success'] == True
