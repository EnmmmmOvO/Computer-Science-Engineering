import pytest
import requests
import json
from src import config

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
    assert u1_payload.status_code == 200
    u1_payload = u1_payload.json()

    return {
        'user' : u1_payload
    }

def test_user_profile_setname_v2(setup):
    setname = requests.put(config.url + 'user/profile/setname/v2', json={
        'token': setup['user']['token'], 
        'name_first': 'Hayden', 
        'name_last': 'Jacobs'
    })
    assert setname.status_code == 200
    resp = requests.get(config.url + 'user/profile/v2', params={
        'token': setup['user']['token'], 
        'u_id': setup['user']['auth_user_id']
    })
    assert resp.status_code == 200
    profile = resp.json().get('user')
    assert profile['name_first'] == 'Hayden'
    assert profile['name_last'] == 'Jacobs'
    
def test_user_profile_setemail_v2(setup):
    setname = requests.put(config.url + 'user/profile/setemail/v2', json={
        'token': setup['user']['token'], 
        'email': 'cs1531@com.au'
    })
    assert setname.status_code == 200
    resp = requests.get(config.url + 'user/profile/v2', params={
        'token': setup['user']['token'], 
        'u_id': setup['user']['auth_user_id']
    })
    assert resp.status_code == 200
    profile = resp.json().get('user')
    assert profile['u_id'] == setup['user']['auth_user_id']
    assert profile['email'] == 'cs1531@com.au'
    
def test_user_profile_sethandle_v1(setup):
    setname = requests.put(config.url + 'user/profile/sethandle/v1', json={
        'token': setup['user']['token'], 
        'handle_str': 'haydenjacobs'
    })
    assert setname.status_code == 200
    resp = requests.get(config.url + 'user/profile/v2', params={
        'token': setup['user']['token'], 
        'u_id': setup['user']['auth_user_id']
    })
    assert resp.status_code == 200
    profile = resp.json().get('user')
    assert profile['u_id'] == setup['user']['auth_user_id']
    assert profile['handle_str'] == 'haydenjacobs'
    
def test_users_all_v1(setup):
    resp = requests.get(config.url + '/users/all/v1', params={
        'token': setup['user']['token']
    })
    assert resp.status_code == 200
    profile = resp.json().get('users')
    assert len(profile) == 1


