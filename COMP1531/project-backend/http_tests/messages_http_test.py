import pytest
import requests
import json
from time import sleep
from datetime import datetime, timezone
from src import config
from src.data import users 

# TEST Notifications as well

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
    
    # Create User 2 - Dreams Member
    u2_payload = requests.post(config.url + "auth/register/v2", json={
        'email': 'banana@com.au', 
        'password': 'password2', 
        'name_first': 'Michael', 
        'name_last': 'Scott'
    })
    assert u2_payload.status_code == 200
    u2_payload = u2_payload.json()

    # User 1 (Dreams Owner) creates Public Channel 1
    c1_payload = requests.post(config.url + "channels/create/v2", json={
        'token': u1_payload['token'], 
        'name': 'channel1', 
        'is_public': True
    })
    assert c1_payload.status_code == 200
    c1_payload = c1_payload.json()

    # User 2 (Dreams Member) creates Private Channel 2
    c2_payload = requests.post(config.url + "channels/create/v2", json={
        'token': u2_payload['token'], 
        'name': 'channel2', 
        'is_public': False
    })
    assert c2_payload.status_code == 200
    c2_payload = c2_payload.json()

    # User 1 (Dreams Owner) creates DM1 with User 2 (also sends a notification)
    dm1_payload = requests.post(config.url + 'dm/create/v1', json={
        'token': u1_payload['token'], 
        'u_ids': [u2_payload['auth_user_id']]
    })
    assert dm1_payload.status_code == 200
    dm1_payload = dm1_payload.json()

    # User 2 (Dreams Member) creates DM2 with User 1
    dm2_payload = requests.post(config.url + 'dm/create/v1', json={
        'token': u2_payload['token'], 
        'u_ids': [u1_payload['auth_user_id']]
    })
    assert dm2_payload.status_code == 200
    dm2_payload = dm2_payload.json()

    return {
        'user1' : u1_payload,
        'user2' : u2_payload,
        'public_channel' : c1_payload['channel_id'],
        'private_channel' : c2_payload['channel_id'],
        'dm1' : dm1_payload['dm_id'],
        'dm2' : dm2_payload['dm_id']
    }

def test_unauthorised_message_sender(setup):

    msg_send = requests.post(config.url + "message/send/v2", json={
        'token': setup['user2']['token'], 
        'channel_id': setup['public_channel'], 
        'message': "I am unauthorised. Let me send a message."
    })
    assert msg_send.status_code == 403

    msg_send_payload = requests.post(config.url + "message/send/v2", json={
        'token': setup['user1']['token'], 
        'channel_id': setup['public_channel'], 
        'message': "I am authorised. Let me in."
    })

    assert msg_send_payload.status_code == 200
    msg_send_payload = msg_send_payload.json()

    msg_edit = requests.put(config.url + "message/edit/v2", json={
        'token': setup['user2']['token'], 
        'message_id': msg_send_payload['message_id'], 
        'message': "I am unauthorised. Let me edit a message."
    })
    assert msg_edit.status_code == 403
    msg_delete = requests.delete(config.url + "message/remove/v1", json={
        'token': setup['user2']['token'], 
        'message_id': msg_send_payload['message_id']
    })
    assert msg_delete.status_code == 403

def test_notifications(setup):
    '''
    Testing notifications for channel invitation and message
    '''
    # User 1 invites User 2 to Public Channel (sending a notification)
    invite_user2 = requests.post(config.url + "channel/invite/v2", json={
        'token': setup['user1']['token'], 
        'channel_id': setup['public_channel'], 
        'u_id': setup['user2']['auth_user_id']
    })
    assert invite_user2.status_code == 200

    msg_send_payload = requests.post(config.url + "message/send/v2", json={
        'token': setup['user1']['token'], 
        'channel_id': setup['public_channel'], 
        'message': "@michaelscott Howw are you?"
    })
    assert msg_send_payload.status_code == 200
    msg_send_payload = msg_send_payload.json()

    notifications_payload = requests.get(config.url + "notifications/get/v1", params={
        'token': setup['user2']['token']})
    assert notifications_payload.status_code == 200
    notifications_payload = notifications_payload.json()
    assert len(notifications_payload['notifications']) == 3

    msg_edit = requests.put(config.url + "message/edit/v2", json={
        'token': setup['user1']['token'], 
        'message_id': msg_send_payload['message_id'], 
        'message': "@michaelscott How are you?"
    })
    assert msg_edit.status_code == 200
    msg_delete = requests.delete(config.url + "message/remove/v1", json={
        'token': setup['user1']['token'], 
        'message_id': msg_send_payload['message_id']
    })
    assert msg_delete.status_code == 200

def test_message_share(setup):

    # User 1 joins Private Channel 2
    c_join = requests.post(config.url + "channel/join/v2", json={
        'token': setup['user1']['token'], 
        'channel_id': setup['private_channel']
    })
    assert c_join.status_code == 200

    # User 1 sends message to Public Channel 1
    msg_id1_payload = requests.post(config.url + "message/send/v2", json={
        'token': setup['user1']['token'], 
        'channel_id': setup['public_channel'], 
        'message': "@michaelscott Howw are you?"
    })
    assert msg_id1_payload.status_code == 200
    msg_id1_payload = msg_id1_payload.json()

    # User 1 sends message to DM1
    msg_id2_payload = requests.post(config.url + "message/senddm/v1", json={
        'token': setup['user1']['token'], 
        'dm_id': setup['dm1'], 
        'message': "Hello World?"
    })
    assert msg_id2_payload.status_code == 200
    msg_id2_payload = msg_id2_payload.json()

    # User 1 shares msg_id1 to Private Channel 2 and msg_id2 to dm2
    msg_share = requests.post(config.url + "message/share/v1", json={
        'token': setup['user1']['token'], 
        'og_message_id': msg_id1_payload['message_id'],
        'channel_id': setup['private_channel'], 
        'dm_id': -1,
        'message': "Stop this madness!"
    })
    assert msg_share.status_code == 200

    msg_share = requests.post(config.url + "message/share/v1", json={
        'token': setup['user1']['token'], 
        'og_message_id': msg_id2_payload['message_id'],
        'channel_id': -1, 
        'dm_id': setup['dm2'],
        'message': "Stop this madness!"
    })
    assert msg_share.status_code == 200

    # Check that a new message has been added to private channel and dm2
    channel_msgs = requests.get(config.url + "channel/messages/v2", params={
            'token': setup['user2']['token'],
            'channel_id': setup['private_channel'],
            'start': 0
    })
    assert channel_msgs.status_code == 200
    channel_msgs = channel_msgs.json()
    assert len(channel_msgs['messages']) == 1

    dm_msgs = requests.get(config.url + "dm/messages/v1", params={
            'token': setup['user2']['token'],
            'dm_id': setup['dm2'],
            'start': 0
    })
    assert dm_msgs.status_code == 200
    dm_msgs = dm_msgs.json()
    assert len(dm_msgs['messages']) == 1


'''
Tests for message/pin/v1 and message/unpin/v1
'''

def test_message_pin_unpin_twice(setup):
    # User 1 sends message to private channel
    msg_send_payload = requests.post(config.url + "message/send/v2", json={
        'token': setup['user1']['token'], 
        'channel_id': setup['public_channel'], 
        'message': "Hello World"
    })
    assert msg_send_payload.status_code == 200
    msg_send_payload = msg_send_payload.json().get('message_id')
    
    # User 1 pins msg_id
    msg_pin = requests.post(config.url + "message/pin/v1", json={
        'token': setup['user1']['token'], 
        'message_id': msg_send_payload
    })
    assert msg_pin.status_code == 200

    # User 1 pins msg_id again
    msg_pin = requests.post(config.url + "message/pin/v1", json={
        'token': setup['user1']['token'], 
        'message_id': msg_send_payload
    })
    assert msg_pin.status_code == 400
    
    # User 1 unpins msg_id
    msg_unpin = requests.post(config.url + "message/unpin/v1", json={
        'token': setup['user1']['token'], 
        'message_id': msg_send_payload
    })
    assert msg_unpin.status_code == 200

    # User 1 unpins msg_id1 again
    msg_unpin = requests.post(config.url + "message/unpin/v1", json={
        'token': setup['user1']['token'], 
        'message_id': msg_send_payload
    })
    assert msg_unpin.status_code == 400

def test_message_pin_unpin_invalid(setup):
    # Test an invalid message id
    msg_pin = requests.post(config.url + "message/pin/v1", json={
        'token': setup['user1']['token'], 
        'message_id': 1
    })
    assert msg_pin.status_code == 400

def test_message_pin_unpin_unauthorised(setup):
    # User 1 sends message to private channel
    msg_id = requests.post(config.url + "message/send/v2", json={
        'token': setup['user1']['token'], 
        'channel_id': setup['public_channel'], 
        'message': "Hello World"
    })
    assert msg_id.status_code == 200
    msg_id = msg_id.json().get('message_id')

    # User 2 tries to pin msg_id1 (not in channel)
    msg_pin = requests.post(config.url + "message/pin/v1", json={
        'token': setup['user2']['token'], 
        'message_id': msg_id
    })
    assert msg_pin.status_code == 403

    invite_user2 = requests.post(config.url + "channel/invite/v2", json={
        'token': setup['user1']['token'], 
        'channel_id': setup['public_channel'], 
        'u_id': setup['user2']['auth_user_id']
    })
    assert invite_user2.status_code == 200

    # User 2 tries to pin msg_id1 (not an owner)   
    msg_pin = requests.post(config.url + "message/pin/v1", json={
        'token': setup['user2']['token'], 
        'message_id': msg_id
    })
    assert msg_pin.status_code == 403

    # User 1 pins the message
    msg_pin = requests.post(config.url + "message/pin/v1", json={
        'token': setup['user1']['token'], 
        'message_id': msg_id
    })
    assert msg_pin.status_code == 200

    # User 2 tries to unpin msg_id1 (not an owner)
    msg_unpin = requests.post(config.url + "message/unpin/v1", json={
        'token': setup['user2']['token'], 
        'message_id': msg_id
    })
    assert msg_unpin.status_code == 403


def test_message_pin_unpin(setup):
    # User 1 sends message to private channel 1 and dm1
    msg_id1 = requests.post(config.url + "message/send/v2", json={
        'token': setup['user2']['token'], 
        'channel_id': setup['private_channel'], 
        'message': "Hello World"
    })
    assert msg_id1.status_code == 200
    msg_id1 = msg_id1.json().get('message_id')

    msg_id2 = requests.post(config.url + "message/senddm/v1", json={
        'token': setup['user1']['token'], 
        'dm_id': setup['dm1'], 
        'message': "Hello World"
    })
    assert msg_id2.status_code == 200
    msg_id2 = msg_id2.json().get('message_id')

    # User 2 (in channel) and User 1 (in dm) pins and unpins messages
    msg_pin = requests.post(config.url + "message/pin/v1", json={
        'token': setup['user2']['token'], 
        'message_id': msg_id1
    })
    assert msg_pin.status_code == 200

    msg_pin = requests.post(config.url + "message/pin/v1", json={
        'token': setup['user1']['token'], 
        'message_id': msg_id2
    })
    assert msg_pin.status_code == 200

    msg_unpin = requests.post(config.url + "message/unpin/v1", json={
        'token': setup['user2']['token'], 
        'message_id': msg_id1
    })
    assert msg_unpin.status_code == 200

    msg_unpin = requests.post(config.url + "message/unpin/v1", json={
        'token': setup['user1']['token'], 
        'message_id': msg_id2
    })
    assert msg_unpin.status_code == 200

    add_owner = requests.post(config.url + "channel/addowner/v1", json={
        'token': setup['user2']['token'],
        'channel_id': setup['private_channel'],
        'u_id': setup['user1']['auth_user_id']
    })
    assert add_owner.status_code == 200

    # User 1 pins message again
    msg_pin = requests.post(config.url + "message/pin/v1", json={
        'token': setup['user1']['token'], 
        'message_id': msg_id1
    })
    assert msg_pin.status_code == 200

    msg_unpin = requests.post(config.url + "message/unpin/v1", json={
        'token': setup['user1']['token'], 
        'message_id': msg_id1
    })
    assert msg_unpin.status_code == 200

def test_message_send_later(setup):
    # User 1 sends message to Public Channel 1 with a 10 second delay
    msg_id1_payload = requests.post(config.url + "message/sendlater/v1", json={
        'token': setup['user1']['token'], 
        'channel_id': setup['public_channel'], 
        'message': "@michaelscott Howw are you?",
        'time_sent': int(datetime.now().replace(tzinfo=timezone.utc).timestamp()) + 10
    })
    assert msg_id1_payload.status_code == 200
    # User 1 sends message to DM1
    msg_id2_payload = requests.post(config.url + "message/sendlaterdm/v1", json={
        'token': setup['user1']['token'], 
        'dm_id': setup['dm1'], 
        'message': "Hello World?",
        'time_sent': int(datetime.now().replace(tzinfo=timezone.utc).timestamp()) + 10
    })
    assert msg_id2_payload.status_code == 200

    # Check that no new messages currently exist in public channel and dm2
    channel_msgs = requests.get(config.url + "channel/messages/v2", params={
            'token': setup['user1']['token'],
            'channel_id': setup['public_channel'],
            'start': 0
    })
    assert channel_msgs.status_code == 200
    channel_msgs = channel_msgs.json()
    assert len(channel_msgs['messages']) == 0
    dm_msgs = requests.get(config.url + "dm/messages/v1", params={
            'token': setup['user1']['token'],
            'dm_id': setup['dm1'],
            'start': 0
    })
    assert dm_msgs.status_code == 200
    dm_msgs = dm_msgs.json()
    assert len(dm_msgs['messages']) == 0

    # Wait 10s
    sleep(10)

    # Check that messages now exist in public channel and dm2
    channel_msgs = requests.get(config.url + "channel/messages/v2", params={
            'token': setup['user1']['token'],
            'channel_id': setup['public_channel'],
            'start': 0
    })
    assert channel_msgs.status_code == 200
    channel_msgs = channel_msgs.json()
    assert len(channel_msgs['messages']) == 1
    dm_msgs = requests.get(config.url + "dm/messages/v1", params={
            'token': setup['user1']['token'],
            'dm_id': setup['dm1'],
            'start': 0
    })
    assert dm_msgs.status_code == 200
    dm_msgs = dm_msgs.json()
    assert len(dm_msgs['messages']) == 1
    
