import pytest
import requests
import json
from src import config

#React id
REACT = 1

import pytest
import requests
import json
from src import config

@pytest.fixture
def setup():
    clear = requests.delete(config.url + 'clear/v1')
    assert clear.status_code == 200

    # Create User 1 - Dreams Owner
    u1 = requests.post(config.url + "auth/register/v2", json={
        'email': 'apple@com.au', 
        'password': 'password1', 
        'name_first': 'Steve', 
        'name_last': 'Jobs'
    })
    assert u1.status_code == 200
    u1 = u1.json()
    
    # Create User 2 - Dreams Member
    u2 = requests.post(config.url + "auth/register/v2", json={
        'email': 'banana@com.au', 
        'password': 'password2', 
        'name_first': 'Michael', 
        'name_last': 'Scott'
    })
    assert u2.status_code == 200
    u2 = u2.json()
    
    # Create User 3 - Dreams Member
    u3 = requests.post(config.url + "auth/register/v2", json={
        'email': 'lemon@com.au', 
        'password': 'password3', 
        'name_first': 'Steven', 
        'name_last': 'Bill',
    })
    assert u3.status_code == 200
    u3 = u3.json()
    
    # User 1 create a channel
    ch1 = requests.post(config.url + "channels/create/v2", json={
        'token': u1['token'], 
        'name': 'channel1',
        'is_public': True,
    })
    assert ch1.status_code == 200
    ch1 = ch1.json()

    # Invite user 2
    ch1_invite = requests.post(config.url + "channel/invite/v2", json={
        'token': u1['token'], 
        'channel_id': ch1['channel_id'],
        'u_id': u2['auth_user_id'],
    })
    assert ch1_invite.status_code == 200
    ch1_invite = ch1_invite.json()

    # User 2 create a dm and add user 1 and user 3 in
    dm2 = requests.post(config.url + "dm/create/v1", json={
        'token': u2['token'], 
        'u_ids': [u1['auth_user_id'], u3['auth_user_id']],
    })
    assert dm2.status_code == 200
    dm2 = dm2.json()

    # User 1 send a message to channel1
    m_u1 = requests.post(config.url + "message/send/v2", json={
        'token': u1['token'], 
        'channel_id': ch1['channel_id'], 
        'message': 'Happy Birthday!',
    })
    assert m_u1.status_code == 200
    m_u1 = m_u1.json()

    # User 2 send a message to dm2
    m_u2 = requests.post(config.url + "message/senddm/v1", json={
        'token': u2['token'], 
        'dm_id': dm2['dm_id'], 
        'message': 'How many people are there?',
    })
    assert m_u2.status_code == 200
    m_u2 = m_u2.json()

    # User 3 send a message to dm2
    m_u3 = requests.post(config.url + "message/senddm/v1", json={
        'token': u3['token'], 
        'dm_id': dm2['dm_id'], 
        'message': 'No class today!',
    })
    assert m_u3.status_code == 200
    m_u3 = m_u3.json()

    return{
        'token1': u1['token'], 
        'token2': u2['token'], 
        'token3': u3['token'],
        'channels': ch1['channel_id'], 
        'dms': dm2['dm_id'],
        'message1': m_u1['message_id'],
        'message2': m_u2['message_id'],
        'message3': m_u3['message_id'],
        'invalid_token': 'eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJzZXNzaW9uX2lkIjoxfQ.bd98kGm7nnfY0FFpDFY2afxbN59JddYQn0-ZP9rNVIg',
    }

'''
message_react_v1
'''
def test_react_invalid_token(setup):
#Token passed is a invalid id
    #clear = requests.delete(config.url + 'clear/v1')
    #assert clear.status_code == 200
    r = requests.post(config.url + 'message/react/v1', json={
        'token': setup['invalid_token'],
        'message_id': 1,
        'react_id': REACT,
    })
    assert r.status_code == 403

def test_react_invalid_message_id(setup):
#message_id is not a valid message within a channel or DM that the authorised user has joined
    r = requests.post(config.url + 'message/react/v1', json={
        'token': setup['token1'],
        'message_id': 1,
        'react_id': REACT,
    })
    assert r.status_code == 400

def test_react_invalid_react_id(setup):
#react_id is not a valid React ID
    r = requests.post(config.url + 'message/react/v1', json={
        'token': setup['token1'],
        'message_id': setup['message1'],
        'react_id': 2,
    })
    assert r.status_code == 400

def test_react_already_react(setup):
#Message with ID message_id already contains an active React with ID react_id from the authorised user
    r = requests.post(config.url + 'message/react/v1', json={
        'token': setup['token1'],
        'message_id': setup['message1'],
        'react_id': REACT,
    })
    assert r.status_code == 200
    r = requests.post(config.url + 'message/react/v1', json={
        'token': setup['token1'],
        'message_id': setup['message1'],
        'react_id': REACT,
    })
    assert r.status_code == 400

def test_react_not_a_member(setup):
#The authorised user is not a member of the channel or DM that the message is within
    r = requests.post(config.url + 'message/react/v1', json={
        'token': setup['token3'],
        'message_id': setup['message1'],
        'react_id': REACT,
    })
    assert r.status_code == 403

def test_react(setup):
#React to messages
    r = requests.post(config.url + 'message/react/v1', json={
        'token': setup['token1'],
        'message_id': setup['message1'],
        'react_id': REACT,
    })
    assert r.status_code == 200

    r = requests.post(config.url + 'message/react/v1', json={
        'token': setup['token2'],
        'message_id': setup['message3'],
        'react_id': REACT,
    })
    assert r.status_code == 200
'''
message_unreact_v1
'''

def test_unreact_invalid_token(setup):
#Token passed is a invalid id
    #clear = requests.delete(config.url + 'clear/v1')
    #assert clear.status_code == 200
    r = requests.post(config.url + 'message/unreact/v1', json={
        'token': setup['invalid_token'],
        'message_id': 1,
        'react_id': REACT,
    })
    assert r.status_code == 403

def test_unreact_invalid_message_id(setup):
#message_id is not a valid message within a channel or DM that the authorised user has joined
    r = requests.post(config.url + 'message/unreact/v1', json={
        'token': setup['token1'],
        'message_id': 1,
        'react_id': REACT,
    })
    assert r.status_code == 400

def test_unreact_invalid_react_id(setup):
#react_id is not a registered React ID
    r = requests.post(config.url + 'message/unreact/v1', json={
        'token': setup['token1'],
        'message_id': setup['message1'],
        'react_id': 2,
    })
    assert r.status_code == 400


def test_unreact_did_not_react(setup):
#Message with ID message_id does not contain an active React with ID react_id from the authorised user
    r = requests.post(config.url + 'message/react/v1', json={
        'token': setup['token2'],
        'message_id': setup['message2'],
        'react_id': REACT,
    })
    assert r.status_code == 200
    r = requests.post(config.url + 'message/unreact/v1', json={
        'token': setup['token2'],
        'message_id': setup['message2'],
        'react_id': REACT,
    })
    assert r.status_code == 200
    r = requests.post(config.url + 'message/unreact/v1', json={
        'token': setup['token2'],
        'message_id': setup['message2'],
        'react_id': REACT,
    })
    assert r.status_code == 400

def test_unreact_not_a_member(setup):
#The authorised user is not a member of the channel or DM that the message is within
    r = requests.post(config.url + 'message/unreact/v1', json={
        'token': setup['token3'],
        'message_id': setup['message1'],
        'react_id': REACT,
    })
    assert r.status_code == 403

def test_unreact(setup):
#React to messages first
    r = requests.post(config.url + 'message/react/v1', json={
        'token': setup['token1'],
        'message_id': setup['message1'],
        'react_id': REACT,
    })
    assert r.status_code == 200

    r = requests.post(config.url + 'message/react/v1', json={
        'token': setup['token2'],
        'message_id': setup['message3'],
        'react_id': REACT,
    })
    assert r.status_code == 200
#Unreact to messages
    r = requests.post(config.url + 'message/unreact/v1', json={
        'token': setup['token1'],
        'message_id': setup['message1'],
        'react_id': REACT,
    })
    assert r.status_code == 200

    r = requests.post(config.url + 'message/unreact/v1', json={
        'token': setup['token2'],
        'message_id': setup['message3'],
        'react_id': REACT,
    })
    assert r.status_code == 200
