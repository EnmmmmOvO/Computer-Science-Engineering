import pytest

from src.auth import auth_register_v1
from src.other import clear_v1
from src.channels import channels_create_v1
from src.channel import channel_invite_v1
from src.message import message_send_v1, message_react_v1, message_unreact_v1, message_channel_check, message_dm_check
from src.error import InputError, AccessError
from src.dm import dm_create_v1

#React id
REACT = 1

@pytest.fixture()
def setup():
    clear_v1()
    #Create 3 users
    user1 = auth_register_v1('apple@com.au', 'password1', 'Steve', 'Jobs')
    user2 = auth_register_v1('banana@com.au', 'password2', 'Steven', 'Jacobs')
    user3 = auth_register_v1('mango@com.au', 'password3', 'Thomas', 'Black')
    #user2 create a channel
    channel2 = channels_create_v1(user2['token'], 'channel2', True)

    #Invite user3 to the channel
    channel_invite_v1(user2['token'], channel2, user3['auth_user_id'])

    #user2 create a dm with user1 and user3 in
    dm2 = dm_create_v1(user2['token'], [user1['auth_user_id'], user3['auth_user_id']])

    #user2 send some messages to channel2 and dm2
    m1 = message_send_v1(user2['token'], channel2, 'hello', True)
    m2 = message_send_v1(user2['token'], channel2, 'Today is hot', True)
    m3 = message_send_v1(user2['token'], dm2['dm_id'], 'Good morning', False)
    #user1 send some messages to and dm2
    m4 = message_send_v1(user1['token'], dm2['dm_id'], 'God bless you', False)

    return {
        'user1': user1, 
        'user2': user2, 
        'user3': user3,
        'channels': channel2, 
        'dms': dm2['dm_id'],
        'message1': m1,
        'message2': m2,
        'message3': m3,
        'message4': m4,
    }

'''
message_react_v1
'''

def test_react_invalid_token():
#Token passed is a invalid id
    with pytest.raises(AccessError):
        invalid_token1 = 'eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJzZXNzaW9uc19pZCI6MX0.VRz789P4O1iWpmqlZupD25REjznk5kB1ICLnPnQaTdI'
        message_react_v1(invalid_token1, 1, REACT)

def test_react_invalid_message_id(setup):
#message_id is not a valid message within a channel or DM that the authorised user has joined
    with pytest.raises(InputError):
        message_react_v1(setup['user1']['token'], 1, REACT)

def test_react_invalid_react_id(setup):
#react_id is not a valid React ID
    with pytest.raises(InputError):
        message_react_v1(setup['user1']['token'], setup['message1'], 2)

def test_react_already_react(setup):
#Message with ID message_id already contains an active React with ID react_id from the authorised user
    message_react_v1(setup['user2']['token'], setup['message3'], REACT)
    with pytest.raises(InputError):
        message_react_v1(setup['user2']['token'], setup['message3'], REACT)

def test_react_not_a_member(setup):
#The authorised user is not a member of the channel or DM that the message is within
    with pytest.raises(AccessError):
        message_react_v1(setup['user1']['token'], setup['message1'], REACT)

def test_react(setup):
#React to messages
    message_react_v1(setup['user2']['token'], setup['message3'], REACT)
    messages3 = message_dm_check(setup['message3'])[1]
    for r in messages3['reacts']:
        if r['react_id'] == REACT:
            assert r['is_this_user_reacted']

    message_react_v1(setup['user3']['token'], setup['message1'], REACT)
    messages1 = message_channel_check(setup['message1'])[1]
    for r in messages1['reacts']:
        if r['react_id'] == REACT:
            assert r['is_this_user_reacted']

'''
message_unreact_v1
'''

def test_unreact_invalid_token():
#Token passed is a invalid token
    with pytest.raises(AccessError):
        invalid_token1 = 'eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJzZXNzaW9uc19pZCI6MX0.VRz789P4O1iWpmqlZupD25REjznk5kB1ICLnPnQaTdI'
        message_unreact_v1(invalid_token1, 1, REACT)

def test_unreact_invalid_message_id(setup):
#message_id is not a valid message within a channel or DM that the authorised user has joined
    with pytest.raises(InputError):
        message_unreact_v1(setup['user1']['token'], 1, REACT)

def test_unreact_invalid_react_id(setup):
#react_id is not a valid React ID
    with pytest.raises(InputError):
        message_unreact_v1(setup['user1']['token'], setup['message1'], 2)

def test_unreact_did_not_react(setup):
#Message with ID message_id does not contain an active React with ID react_id from the authorised user
    with pytest.raises(InputError):
        message_unreact_v1(setup['user2']['token'], setup['message3'], REACT)

def test_unreact_not_a_member(setup):
#The authorised user is not a member of the channel or DM that the message is within
    with pytest.raises(AccessError):
        message_unreact_v1(setup['user1']['token'], setup['message1'], REACT)

def test_unreact(setup):
#React to messages
    message_react_v1(setup['user2']['token'], setup['message3'], REACT)
    messages3 = message_dm_check(setup['message3'])[1]
    for r in messages3['reacts']:
        if r['react_id'] == REACT:
            assert r['u_ids'] == [setup['user2']['auth_user_id']]
            assert r['is_this_user_reacted']

    message_react_v1(setup['user3']['token'], setup['message1'], REACT)
    messages1 = message_channel_check(setup['message1'])[1]
    for r in messages1['reacts']:
        if r['react_id'] == REACT:
            assert r['u_ids'] == [setup['user3']['auth_user_id']]
            assert r['is_this_user_reacted']

#Unreact to messages
    message_unreact_v1(setup['user2']['token'], setup['message3'], REACT)
    messages3 = message_dm_check(setup['message3'])[1]
    for r in messages3['reacts']:
        if r['react_id'] == REACT:
            assert r['u_ids'] == []
            assert not r['is_this_user_reacted']

    message_unreact_v1(setup['user3']['token'], setup['message1'], REACT)
    messages1 = message_channel_check(setup['message1'])[1]
    for r in messages1['reacts']:
        if r['react_id'] == REACT:
            assert r['u_ids'] == []
            assert not r['is_this_user_reacted']
