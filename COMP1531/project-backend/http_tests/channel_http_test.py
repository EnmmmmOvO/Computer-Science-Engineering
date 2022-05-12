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
    u1_payload = u1.json()
    
    # Create User 2 - Dreams Member
    u2 = requests.post(config.url + "auth/register/v2", json={
        'email': 'banana@com.au', 
        'password': 'password2', 
        'name_first': 'Michael', 
        'name_last': 'Scott'
    })
    assert u2.status_code == 200
    u2_payload = u2.json()

    # User 1 (Dreams Owner) creates Public Channel 1
    c1 = requests.post(config.url + "channels/create/v2", json={
        'token': u1_payload['token'], 
        'name': 'channel1', 
        'is_public': True
    })
    assert c1.status_code == 200
    c1_payload = c1.json()

    return {
        'user1' : u1_payload,
        'user2' : u2_payload,
        'public_channel' : c1_payload['channel_id']
    }
    
def test_channel_join(setup):
    '''
    Testing server functionality of channel/join/v2 and channel/details/v2
    '''

    c1_join = requests.post(config.url + "channel/join/v2", json={
        'token': setup['user2']['token'],
        'channel_id': setup['public_channel']
    })
    assert c1_join.status_code == 200

    c1_detail = requests.get(config.url + "channel/details/v2", params={
        'token' : setup['user1']['token'], 
        'channel_id' : setup['public_channel']
    })
    assert c1_detail.status_code == 200
    c1_detail_payload = c1_detail.json()

    u1_info = {
        'u_id': setup['user1']['auth_user_id'],
        'email': 'apple@com.au',
        'name_first': 'Steve',
        'name_last': 'Jobs',
        'handle_str': 'stevejobs'
    }

    u2_info = {
        'u_id': setup['user2']['auth_user_id'],
        'email': 'banana@com.au',
        'name_first': 'Michael',
        'name_last': 'Scott',
        'handle_str': 'michaelscott'
    }

    assert u1_info in c1_detail_payload["all_members"] and u2_info in c1_detail_payload["all_members"]

def test_channel_invite(setup):
    '''
    Testing server functionality of channel/invite/v2 and channels/list/v2
    '''

    c1_invite = requests.post(config.url + "channel/invite/v2", json={
        'token': setup['user1']['token'],
        'channel_id': setup['public_channel'],
        'u_id': setup['user2']['auth_user_id']
    })
    assert c1_invite.status_code == 200

    c1_list = requests.get(config.url + "channels/list/v2", \
        params={'token' : setup['user2']['token']})
    assert c1_list.status_code == 200
    c1_list_payload = c1_list.json()

    c1_info = {
        'channel_id': setup['public_channel'],
        'name': 'channel1'
    }

    assert c1_info in c1_list_payload['channels']

def test_channel_message(setup):
    '''
    Testing server functionality of channel/invite/v2 and channels/list/v2
    '''

    # Send 120 messages to public channel
    i = 0
    while i < 120:
        msg_send = requests.post(config.url + "message/send/v2", json={
            'token': setup['user1']['token'],
            'channel_id': setup['public_channel'],
            'message': "Hi"
        })
        assert msg_send.status_code == 200
        i += 1
    
    ret = requests.get(config.url + "channel/messages/v2", params={
            'token': setup['user1']['token'],
            'channel_id': setup['public_channel'],
            'start': 0
    })
    assert ret.status_code == 200
    ret = ret.json()
    assert ret['start'] == 0 and ret['end'] == 50
    ret = requests.get(config.url + "channel/messages/v2", params={
            'token': setup['user1']['token'],
            'channel_id': setup['public_channel'],
            'start': 50
    })
    assert ret.status_code == 200
    ret = ret.json()
    assert ret['start'] == 50 and ret['end'] == 100
    ret = requests.get(config.url + "channel/messages/v2", params={
            'token': setup['user1']['token'],
            'channel_id': setup['public_channel'],
            'start': 100
    })
    assert ret.status_code == 200
    ret = ret.json()
    assert ret['start'] == 100 and ret['end'] == -1


def test_channel_leave(setup):
    '''
    Testing server functionality of channel/invite/v1 
    Checks if a member that has been invited can leave the channel.
    '''

    #invite user2 to the channel 
    user2_invite = requests.post(config.url + "channel/invite/v2", json={
        'token': setup['user1']['token'],
        'channel_id': setup['public_channel'],
        'u_id': setup['user2']['auth_user_id']
    })
    assert user2_invite.status_code == 200

    #make user2 leave channel,
    c1_leave = requests.post(config.url + "channel/leave/v1", json={
        'token': setup['user2']['token'],
        'channel_id': setup['public_channel']
    })
    assert c1_leave.status_code == 200

    #check the channel details
    c1_details = requests.get(config.url + "channel/details/v2",params={
        'token': setup['user1']['token'],
        'channel_id': setup['public_channel']
    })
    assert c1_details.status_code == 200
    c1_details_payload = c1_details.json()

    #since user 2 should not be found as part of all_members; there should only be 1 member in channel 
    assert len(c1_details_payload['all_members']) == 1

def test_channel_addowner(setup):
    '''
    Testing server functionality of channel/addowner/v1
    Check if new owner can be added 
    '''

    #add user2 as owner     
    u2_owner = requests.post(config.url + "channel/addowner/v1", json={
        'token': setup['user1']['token'],
        'channel_id': setup['public_channel'],
        'u_id': setup['user2']['auth_user_id']
    })
    assert u2_owner.status_code == 200

    #check the channel details 
    c1_details = requests.get(config.url + "channel/details/v2",params={
        'token': setup['user1']['token'],
        'channel_id': setup['public_channel'],
    })
    assert c1_details.status_code == 200
    c1_details_payload = c1_details.json()

    #since user2 was added, the number of owner_members should be 2
    assert len(c1_details_payload['owner_members']) == 2



def test_channel_listall(setup):
    '''
    Testing server functionality of channel/listall/v2
    '''

    c_listall = requests.get(config.url + "channels/listall/v2", \
                        params={'token' : setup['user1']['token']})
    assert c_listall.status_code == 200
    c_listall_payload = c_listall.json()

    c_info = {
        'channel_id': setup['public_channel'],
        'name': 'channel1'
    }

    assert c_info in c_listall_payload['channels']

def test_channel_removeowner(setup):
    '''
    Testing server functionality of channel/removeowner/v1
    Check if owner can be removed
    '''
    #add user2 as owner     
    u2_owner = requests.post(config.url + "channel/addowner/v1", json={
        'token': setup['user1']['token'],
        'channel_id': setup['public_channel'],
        'u_id': setup['user2']['auth_user_id']
    })
    assert u2_owner.status_code == 200

    #remove user 2 as owner 
    u2_removeowner = requests.post(config.url + "channel/removeowner/v1", json={
        'token': setup['user1']['token'],
        'channel_id': setup['public_channel'],
        'u_id': setup['user2']['auth_user_id']
    })
    assert u2_removeowner.status_code == 200

    #check the channel details
    c1_details = requests.get(config.url + "/channel/details/v2",params={
        'token': setup['user1']['token'],
        'channel_id': setup['public_channel'],
    })
    assert c1_details.status_code == 200
    c1_details_payload = c1_details.json()

    # Since user2 has been removed as owner, there should only be 1 owner_member
    assert len(c1_details_payload['owner_members']) == 1

    