import pytest
import requests
import json
from src import config

#permission_id
OWNER = 1
MEMBER = 2

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
    
    # Create User 3
    u3_payload = requests.post(config.url + "auth/register/v2", json={
        'email': 'lemon@com.au', 
        'password': 'password3', 
        'name_first': 'Aiden', 
        'name_last': 'Josh'
    })
    u3_payload = u3_payload.json()
    return {
        'user1' : u1_payload,
        'user2' : u2_payload,
        'user3' : u3_payload,
        'invalid_token' : 'eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJzZXNzaW9uc19pZCI6MX0.VRz789P4O1iWpmqlZupD25REjznk5kB1ICLnPnQaTdI'
    }


'''
admin_user_remove_v1
'''
def test_invalid_token_remove(setup):
    #Token passed is a invalid token
    r = requests.delete(config.url + 'admin/user/remove/v1', json={
        'token': setup['invalid_token'],
        'u_id': setup['user2']['auth_user_id'],
    })
    assert r.status_code == 403

def test_invalid_u_id_remove(setup):
    #u_id is invalid
    r = requests.delete(config.url + 'admin/user/remove/v1', json={
        'token': setup['user1']['token'],
        'u_id': 4,
    })
    assert r.status_code == 400
    r = requests.delete(config.url + 'admin/user/remove/v1', json={
        'token': setup['user1']['token'],
        'u_id': -2,
    })
    assert r.status_code == 400

def test_only_owner(setup):
    #The user is currently the only owner
    r = requests.delete(config.url + 'admin/user/remove/v1', json={
        'token': setup['user1']['token'],
        'u_id': setup['user1']['auth_user_id'],
    })
    assert r.status_code == 400

def test_not_owner_remove(setup):
    #The authorised user is not an owner
    r = requests.delete(config.url + 'admin/user/remove/v1', json={
        'token': setup['user2']['token'],
        'u_id': setup['user2']['auth_user_id'],
    })
    assert r.status_code == 403

def test_remove(setup):
    #remove a user and change his message to 'Removed user'
    r = requests.delete(config.url + 'admin/user/remove/v1', json={
        'token': setup['user1']['token'],
        'u_id': setup['user3']['auth_user_id'],
    })
    assert r.status_code == 200

'''
admin_userpermission_change_v1
'''

def test_invalid_token_change(setup):
    #Token passed is a invalid id
    upc = requests.post(config.url + 'admin/userpermission/change/v1', json={
        'token': setup['invalid_token'],
        'u_id': setup['user2']['auth_user_id'],
        'permission_id': OWNER,
    })
    assert upc.status_code == 403

def test_invalid_u_id_change(setup):
    #u_id is invalid
    upc = requests.post(config.url + 'admin/userpermission/change/v1', json={
        'token': setup['user1']['token'],
        'u_id': 4,
        'permission_id': OWNER,
    })
    assert upc.status_code == 400

    upc = requests.post(config.url + 'admin/userpermission/change/v1', json={
        'token': setup['user1']['token'],
        'u_id': -2,
        'permission_id': OWNER,
    })
    assert upc.status_code == 400

def test_invalid_permission_id(setup):
    #permission_id is invalid
    upc = requests.post(config.url + 'admin/userpermission/change/v1', json={
        'token': setup['user1']['token'],
        'u_id': setup['user2']['auth_user_id'],
        'permission_id': 3,
    })
    assert upc.status_code == 400

    upc = requests.post(config.url + 'admin/userpermission/change/v1', json={
        'token': setup['user1']['token'],
        'u_id': setup['user2']['auth_user_id'],
        'permission_id': -2,
    })
    assert upc.status_code == 400

def test_not_owner_change(setup):
    #The authorised user is not an owner
    upc = requests.post(config.url + 'admin/userpermission/change/v1', json={
        'token': setup['user2']['token'],
        'u_id': setup['user1']['auth_user_id'],
        'permission_id': MEMBER,
    })
    assert upc.status_code == 403

def test_change(setup):
    #User1 change permission id of user2
    upc = requests.post(config.url + 'admin/userpermission/change/v1', json={
        'token': setup['user1']['token'],
        'u_id': setup['user2']['auth_user_id'],
        'permission_id': OWNER,
    })
    assert upc.status_code == 200
    #User2 change permission id of user1
    upc = requests.post(config.url + 'admin/userpermission/change/v1', json={
        'token': setup['user2']['token'],
        'u_id': setup['user1']['auth_user_id'],
        'permission_id': MEMBER,
    })
    assert upc.status_code == 200
