import pytest
import requests
import json
import time
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

    c = requests.post(config.url + "channels/create/v2", json={
        'token': u1_payload['token'], 
        'name': 'channel1', 
        'is_public': True
    })
    assert c.status_code == 200
    c_payload = c.json()

    c_invite = requests.post(config.url + "channel/invite/v2", json={
        'token': u1_payload['token'],
        'channel_id': c_payload['channel_id'],
        'u_id': u2_payload['auth_user_id']
    })
    assert c_invite.status_code == 200

    return {
        'sample_user1': u1_payload,
        'sample_user2': u2_payload,
        'sample_channel_id': c_payload['channel_id'],
    }


def test_standup_start(setup):
    resp = requests.post(config.url + 'standup/start/v1', json={
        'token': setup['sample_user1']['token'], 
        'channel_id': setup['sample_channel_id'],
        'length': 0.001
    })
    assert resp.status_code == 200
    assert json.loads(resp.text)['time_finished']


def test_standup_active(setup):
    resp = requests.get(config.url + 'standup/active/v1', params={
        'token': setup['sample_user1']['token'], 
        'channel_id': setup['sample_channel_id'],
    })
    assert resp.status_code == 200
    assert json.loads(resp.text)['is_active'] == False

    resp = requests.post(config.url + 'standup/start/v1', json={
        'token': setup['sample_user1']['token'], 
        'channel_id': setup['sample_channel_id'],
        'length': 5
    })
    assert resp.status_code == 200
    assert json.loads(resp.text)['time_finished']

    resp = requests.get(config.url + 'standup/active/v1', params={
        'token': setup['sample_user1']['token'], 
        'channel_id': setup['sample_channel_id'],
    })
    assert resp.status_code == 200
    assert json.loads(resp.text)['is_active'] == True

    time.sleep(5)
    resp = requests.get(config.url + 'standup/active/v1', params={
        'token': setup['sample_user1']['token'], 
        'channel_id': setup['sample_channel_id'],
    })
    assert resp.status_code == 200
    assert json.loads(resp.text)['is_active'] == False


def test_standup_send(setup):
    message_str1 = 'this is a message from sample user 1'
    message_str2 = 'this is a message from sample user 2'

    resp = requests.post(config.url + 'standup/start/v1', json={
        'token': setup['sample_user1']['token'], 
        'channel_id': setup['sample_channel_id'],
        'length': 5
    })
    assert resp.status_code == 200
    assert json.loads(resp.text)['time_finished']

    resp = requests.post(config.url + 'standup/send/v1', json={
        'token': setup['sample_user1']['token'], 
        'channel_id': setup['sample_channel_id'],
        'message': message_str1
    })
    assert resp.status_code == 200
    resp = requests.post(config.url + 'standup/send/v1', json={
        'token': setup['sample_user2']['token'], 
        'channel_id': setup['sample_channel_id'],
        'message': message_str2
    })
    assert resp.status_code == 200

    time.sleep(5)
    resp = requests.get(config.url + 'channel/messages/v2', params={
        'token': setup['sample_user1']['token'], 
        'channel_id': setup['sample_channel_id'],
        'start': 0
    })
    assert resp.status_code == 200
    answer = json.loads(resp.text)['messages']
    answer = [ans['message'] for ans in answer]
    assert answer == [message_str2, message_str1]
