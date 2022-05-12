'''
Tests for channel_
Bak: channel/leave, channel/add-wner, channel/remove_owner
'''
import pytest

from src.auth import auth_register_v1
from src.channel import channel_invite_v1, channel_details_v1, \
        channel_leave_v1,channel_join_v1, channel_addowner_v1, \
        channel_removeowner_v1
from src.channels import channels_create_v1, channels_list_v1
from src.error import InputError, AccessError
from src.other import clear_v1
import time

@pytest.fixture
def setup():
    '''
    Initialises internal data of application and creates two users, two private channels
    and one public channel.
    '''
    clear_v1()
    user1 = auth_register_v1('apple@com.au', 'password1', 'Steve', 'Jobs')
    user2 = auth_register_v1('banana@com.au', 'password2', 'Steven', 'Jacobs')
    channel1 = channels_create_v1(user1['token'], 'channel1', False)
    time.sleep(0.001) # interval for helper.uniqid generation
    channel2 = channels_create_v1(user1['token'], 'channel2', True)
    time.sleep(0.001) # interval for helper.uniqid generation
    channel3 = channels_create_v1(user2['token'], 'channel3', False)
    return {
        'sample_user1' : {'token' : user1['token'], 'auth_user_id' : user1['auth_user_id']},
        'sample_user2' : {'token' : user2['token'], 'auth_user_id' : user2['auth_user_id']}, 
        'private_channel' : channel1,
        'public_channel' : channel2,
        'private_channel2' : channel3,
        'invalid_token1' : 'eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJzZXNzaW9uc19pZCI6MX0.VRz789P4O1iWpmqlZupD25REjznk5kB1ICLnPnQaTdI'
    }

def test_channel_details_v1(setup):
    
    answer = {
        'name': 'channel1',
        'owner_members': [
            {
                'u_id': setup['sample_user1']['auth_user_id'],
                'email': 'apple@com.au',
                'name_first': 'Steve',
                'name_last': 'Jobs',
                'handle_str': 'stevejobs'
            }
        ],
        'all_members': [
            {
                'u_id': setup['sample_user1']['auth_user_id'],
                'email': 'apple@com.au',
                'name_first': 'Steve',
                'name_last': 'Jobs',
                'handle_str': 'stevejobs'
            }
        ],
        'is_public' : False
    }

    # test case: user 1 access details of channel 1
    assert channel_details_v1(setup['sample_user1']['token'], setup['private_channel']) == answer
    
def test_channel_details_v1_except(setup):
    with pytest.raises(AccessError):
        # test case: auth_user_id does not refer to a valid user
        channel_details_v1(setup['invalid_token1'], setup['private_channel'])
    with pytest.raises(AccessError):
        # test case: auth_user_id is not a member of channel with channel_id
        channel_details_v1(setup['sample_user2']['token'], setup['public_channel'])
    
    # test case: channel_id is not a valid channel
    with pytest.raises(InputError):
        channel_details_v1(setup['sample_user1']['token'], -1)


def test_channel_leave_v1(setup):
    assert channel_join_v1(setup['sample_user2']['token'], setup['public_channel']) == {}
    assert channel_leave_v1(setup['sample_user2']['token'], setup['public_channel']) == {}
    assert channel_leave_v1(setup['sample_user1']['token'], setup['public_channel']) == {}

def test_channel_leave_v1_except(setup):
    with pytest.raises(AccessError):
        # test case: auth_user_id does not refer to a valid user
        channel_leave_v1(setup['invalid_token1'], setup['private_channel'])
    with pytest.raises(AccessError):
        # test case: auth_user_id is not a member of channel with channel_id
        channel_leave_v1(setup['sample_user2']['token'], setup['public_channel'])

    with pytest.raises(InputError):
        # test case: channel_id does not refer to a valid channel 
        channel_leave_v1(setup['sample_user1']['token'], 0)

def test_channel_addowner_removeowner_v1(setup):
    assert channel_addowner_v1(setup['sample_user1']['token'], setup['private_channel'], setup['sample_user2']['auth_user_id']) == {}
    assert channel_removeowner_v1(setup['sample_user1']['token'], setup['private_channel'], setup['sample_user2']['auth_user_id']) == {}
    assert channel_addowner_v1(setup['sample_user1']['token'], setup['private_channel'], setup['sample_user2']['auth_user_id']) == {}

def test_channel_addowner_v1_except(setup):
    with pytest.raises(AccessError):
        # test case: auth_user_id does not refer to a valid user
        channel_addowner_v1(setup['invalid_token1'], setup['private_channel'], setup['sample_user1']['auth_user_id'])
    with pytest.raises(AccessError):
        # test case: auth_user_id is not a member of channel with channel_id
        channel_addowner_v1(setup['sample_user2']['token'], setup['public_channel'], setup['sample_user1']['auth_user_id'])

    with pytest.raises(InputError):
        # test case: channel_id does not refer to a valid channel 
        channel_addowner_v1(setup['sample_user1']['token'], 0, setup['sample_user2']['auth_user_id'])
    with pytest.raises(InputError):
        # test case: u_id does not refer to a valid user
        channel_addowner_v1(setup['sample_user1']['token'], setup['private_channel'], 0)
    with pytest.raises(InputError):
        # test case: u_id already owner
        channel_addowner_v1(setup['sample_user1']['token'], setup['private_channel'], setup['sample_user1']['auth_user_id'])

def test_channel_removeowner_v1(setup):
    channel_addowner_v1(setup['sample_user1']['token'], setup['private_channel'], setup['sample_user2']['auth_user_id'])
    assert channel_removeowner_v1(setup['sample_user1']['token'], setup['private_channel'], setup['sample_user2']['auth_user_id']) == {}

def test_channel_removeowner_v1_except(setup):
    with pytest.raises(AccessError):
        # test case: auth_user_id does not refer to a valid user
        channel_removeowner_v1(setup['invalid_token1'], setup['private_channel'], setup['sample_user1']['auth_user_id'])
    with pytest.raises(AccessError):
        # test case: auth_user_id is not a member of channel with channel_id
        channel_removeowner_v1(setup['sample_user2']['token'], setup['public_channel'], setup['sample_user1']['auth_user_id'])

    with pytest.raises(InputError):
        # test case: channel_id does not refer to a valid channel 
        channel_removeowner_v1(setup['sample_user1']['token'], 0, setup['sample_user2']['auth_user_id'])
    with pytest.raises(InputError):
        # test case: u_id does not refer to a valid user
        channel_removeowner_v1(setup['sample_user1']['token'], setup['private_channel'], 0)
    with pytest.raises(InputError):
        # test case: u_id already not owner
        channel_removeowner_v1(setup['sample_user1']['token'], setup['private_channel'], setup['sample_user2']['auth_user_id'])
    with pytest.raises(InputError):
        # test case: u_id only owner
        channel_removeowner_v1(setup['sample_user1']['token'], setup['private_channel'], setup['sample_user1']['auth_user_id'])


def test_channel_invite_v1(setup):

    # user 1 - private channel 1
    # user 1 - public channel 2
    # user 2 - private channel 3

    # test case: user 1 invites user 1 into channel 1
    assert channel_invite_v1(setup['sample_user1']['token'], setup['private_channel'], setup['sample_user1']['auth_user_id']) == {}
    # test case: user 1 invites user 2 into channel 1
    assert channel_invite_v1(setup['sample_user1']['token'], setup['private_channel'], setup['sample_user2']['auth_user_id']) == {}

    # test case: user 2 invites user 1 into channel 1
    assert channel_invite_v1(setup['sample_user2']['token'], setup['private_channel'], setup['sample_user1']['auth_user_id']) == {}

    # test case: user 2 invites user 1 into channel 3
    assert channel_invite_v1(setup['sample_user2']['token'], setup['private_channel2'], setup['sample_user1']['auth_user_id']) == {}

    # test case: user 2 invites user 2 into channel 1
    assert channel_invite_v1(setup['sample_user2']['token'], setup['private_channel'], setup['sample_user2']['auth_user_id']) == {}

    # test case: user 1 invites user 2 into channel 2
    assert channel_invite_v1(setup['sample_user1']['token'], setup['public_channel'], setup['sample_user2']['auth_user_id']) == {}

def test_channel_invite_v1_except(setup):
    with pytest.raises(AccessError):
        # test case: auth_user_id does not refer to a valid user
        channel_invite_v1(setup['invalid_token1'], setup['private_channel'], setup['sample_user1']['auth_user_id'])
    with pytest.raises(AccessError):
        # test case: auth_user_id is not a member of channel with channel_id
        channel_invite_v1(setup['sample_user2']['token'], setup['public_channel'], setup['sample_user1']['auth_user_id'])

    with pytest.raises(InputError):
        # test case: channel_id does not refer to a valid channel 
        channel_invite_v1(setup['sample_user1']['token'], 0, setup['sample_user2']['auth_user_id'])
    with pytest.raises(InputError):
        # test case: u_id does not refer to a valid user
        channel_invite_v1(setup['sample_user1']['token'], setup['private_channel'], 0)

