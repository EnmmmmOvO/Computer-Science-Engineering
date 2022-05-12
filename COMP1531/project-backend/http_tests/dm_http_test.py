import pytest
import requests
import json
from src import config
from src.error import InputError, AccessError

@pytest.fixture
def setup():
    clear = requests.delete(config.url + 'clear/v1')
    assert clear.status_code == 200
    
    u1_payload = requests.post(config.url + "auth/register/v2", json={
        'email': 'apple@com.au', 
        'password': 'password1', 
        'name_first': 'Steve', 
        'name_last': 'Jobs'
    })
    assert u1_payload.status_code == 200
    u1_payload = u1_payload.json()

    u2_payload = requests.post(config.url + "auth/register/v2", json={
        'email': 'banana@com.au', 
        'password': 'password2', 
        'name_first': 'Steven', 
        'name_last': 'Jacobs'
    })
    assert u2_payload.status_code == 200
    u2_payload = u2_payload.json()

    u3_payload = requests.post(config.url + "auth/register/v2", json={
        'email': 'cherry@com.au', 
        'password': 'password3', 
        'name_first': 'Sarah', 
        'name_last': 'Jane'
    })
    assert u3_payload.status_code == 200
    u3_payload = u3_payload.json()

    dm1_payload = requests.post(config.url + 'dm/create/v1', json={
        'token': u1_payload['token'], 
        'u_ids': [u2_payload['auth_user_id'], u3_payload['auth_user_id']]
    })
    assert dm1_payload.status_code == 200
    dm1_payload = dm1_payload.json()

    dm2_payload = requests.post(config.url + 'dm/create/v1', json={
        'token': u2_payload['token'], 
        'u_ids': [u3_payload['auth_user_id']]
    })
    assert dm2_payload.status_code == 200
    dm2_payload = dm2_payload.json()

    return {
        'sample_user1': u1_payload,
        'sample_user2': u2_payload,
        'sample_user3': u3_payload,
        'invalid_token': 'eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJzZXNzaW9uc19pZCI6MX0.VRz789P4O1iWpmqlZupD25REjznk5kB1ICLnPnQaTdI',
        'sample_dm1': dm1_payload,
        'sample_dm2': dm2_payload
    }


def test_dm_create(setup):
    resp = requests.post(config.url + 'dm/create/v1', json={
        'token': setup['sample_user1']['token'], 
        'u_ids': [setup['sample_user3']['auth_user_id']]
    })
    assert resp.status_code == 200
    assert json.loads(resp.text)


def test_dm_remove(setup):
    resp = requests.delete(config.url + 'dm/remove/v1', json={
        'token': setup['sample_user1']['token'], 
        'dm_id': setup['sample_dm1']['dm_id']
    })
    assert resp.status_code == 200
    assert json.loads(resp.text) == {}


def test_dm_details(setup):
    '''
    A test to dm_details
    '''
    answer = {'name': setup['sample_dm1']['dm_name'], 'members': [setup['sample_user2']['auth_user_id'], setup['sample_user3']['auth_user_id']]}

    params = {'token': setup['sample_user1']['token'], 'dm_id': setup['sample_dm1']['dm_id']}
    resp = requests.get(config.url + 'dm/details/v1', params=params)
    assert resp.status_code == 200
    assert json.loads(resp.text) == answer

    params = {'token': setup['sample_user2']['token'], 'dm_id': setup['sample_dm1']['dm_id']}
    resp = requests.get(config.url + 'dm/details/v1', params=params)
    assert resp.status_code == 200
    assert json.loads(resp.text) == answer


def test_dm_list(setup):
    '''
    A test to dm_list
    '''
    answer = [
        {
            'dm_id': setup['sample_dm1']['dm_id'],
            'name': setup['sample_dm1']['dm_name']
        },
        {
            'dm_id': setup['sample_dm2']['dm_id'],
            'name': setup['sample_dm2']['dm_name']
        },
    ]
    params = {'token': setup['sample_user3']['token']}
    resp = requests.get(config.url + 'dm/list/v1', params=params)
    assert resp.status_code == 200
    assert json.loads(resp.text).get('dms') == answer


def test_dm_leave(setup):
    '''
    A test for dm_leave
    '''
    resp = requests.post(config.url + 'dm/leave/v1', json={
        'token': setup['sample_user1']['token'], 
        'dm_id': setup['sample_dm1']['dm_id']
    })
    assert resp.status_code == 200
    assert json.loads(resp.text) == {}


def test_dm_invite(setup):
    '''
    A test to dm_invite
    '''
    params = {'token': setup['sample_user1']['token'], 'dm_id': setup['sample_dm1']['dm_id'], 'u_id': setup['sample_user3']['auth_user_id']}
    resp = requests.post(config.url + 'dm/invite/v1', json=params)
    assert resp.status_code == 200
    assert json.loads(resp.text) == {}


def test_dm_messages(setup):
    '''
    A test for dm_messages
    '''

    answer = {
        'messages': [],
        'start': 0,
        'end': -1
    }

    resp = requests.get(config.url + 'dm/messages/v1', params={
        'token': setup['sample_user1']['token'], 
        'dm_id': setup['sample_dm1']['dm_id'], 
        'start': 0
    })
    assert resp.status_code == 200
    assert json.loads(resp.text) == answer
    

