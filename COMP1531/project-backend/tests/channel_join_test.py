'''
This file specifies a range of test functions for the channel features by utilising
pytest fixtures that assume proper functionality of functions such as auth_register_v1
and channels_create_v1. All internal data is reset to the initial state before each pytest
to make simpler, less error-prone tests.
'''

import pytest

# from src.data import users, channels
from src.auth import auth_register_v1
from src.channel import channel_join_v1
from src.channels import channels_create_v1, channels_list_v1
from src.error import InputError, AccessError
from src.other import clear_v1
import src.helper as helper
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
        'sample_user1' : user1['token'],
        'sample_user2' : user2['token'], 
        'private_channel' : channel1,
        'public_channel' : channel2,
        'private_channel2' : channel3,
    }   

# Test channel_join_v1

def test_user_invalid(setup):
    '''
    Tests if channel_join_v1() raises AccessError exception after being given
    an invalid auth_user_id.
    '''
    invalid_token1 = 'eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJzZXNzaW9uc19pZCI6MX0.VRz789P4O1iWpmqlZupD25REjznk5kB1ICLnPnQaTdI'
    with pytest.raises(AccessError):
        # User does not exist
        assert channel_join_v1(invalid_token1, setup['public_channel'])

def test_channel_invalid(setup):
    '''
    Tests if channel_join_v1() raises InputError exception after being given
    an invalid channel_id.
    '''
    with pytest.raises(InputError):
        # Channel -1 do not exist
        assert channel_join_v1(setup['sample_user1'], -1)
    with pytest.raises(InputError):
        # Channel 10 do not exist
        assert channel_join_v1(setup['sample_user1'], 10)

def test_channel_no_join_permissions(setup):
    '''
    Tests if channel_join_v1() raises AccessError exception if sample_user2 (who is
    not a global owner) attempts to join a private channel.
    '''
    with pytest.raises(AccessError):
        assert channel_join_v1(setup['sample_user2'], setup['private_channel'])

def test_channel_with_join_permissions(setup):
    '''
    Tests if channel_join_v1() adds members not already added to public_channel.
    '''    

    assert channel_join_v1(setup['sample_user2'], setup['public_channel']) == {}
    
    channel_info = helper.channel_info(setup['public_channel'])
    assert channel_info in channels_list_v1(setup['sample_user2'])

def test_global_owner_join_permissions(setup):
    '''
    Tests if channel_join_v1() allows a global owner to join a private channel if not already a member.
    '''

    assert channel_join_v1(setup['sample_user1'], setup['private_channel2']) == {}
    
    channel_info = helper.channel_info(setup['private_channel2'])
    assert channel_info in channels_list_v1(setup['sample_user1'])

