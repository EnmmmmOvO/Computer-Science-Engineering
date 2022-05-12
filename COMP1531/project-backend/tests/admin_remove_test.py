import pytest
import json

from src.data import users, channels
from src.error import InputError, AccessError
from src.auth import auth_register_v1
from src.admin import admin_user_remove_v1, admin_userpermission_change_v1
from src.other import clear_v1
from src.channels import channels_create_v1
from src.channel import channel_join_v1
from src.channel import channel_messages_v1
from src.message import message_send_v1
from src.user import user_profile_v2
#Permission id
OWNER = 1
MEMBER = 2

@pytest.fixture()
def setup():
    clear_v1()
    user1 = auth_register_v1('apple@com.au', 'password1', 'Steve', 'Jobs')
    user2 = auth_register_v1('banana@com.au', 'password2', 'Steven', 'Jacobs')
    user3 = auth_register_v1('mango@com.au', 'password3', 'Thomas', 'Black')
    admin_userpermission_change_v1(user1['token'], 3, OWNER)
    channel2 = channels_create_v1(user2['token'], 'channel2', True)
    message_send_v1(user2['token'], channel2, 'hello', True)
    return{
        'user1': user1, 
        'user2': user2, 
        'user3': user3,
        'channels': channel2, 
    }

def test_invalid_token():
#Token passed is a invalid id
    with pytest.raises(AccessError):
        invalid_token1 = 'eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJzZXNzaW9uc19pZCI6MX0.VRz789P4O1iWpmqlZupD25REjznk5kB1ICLnPnQaTdI'
        admin_user_remove_v1(invalid_token1, 2)
        
def test_invalid_u_id(setup):
#u_id is invalid
    with pytest.raises(InputError):
        admin_user_remove_v1(setup['user1']['token'], -1)
    with pytest.raises(InputError):
        admin_user_remove_v1(setup['user1']['token'], 123456)

def test_only_owner(setup):
#The user is currently the only owner

    with pytest.raises(InputError):
        admin_user_remove_v1(setup['user3']['token'], 3)
        admin_user_remove_v1(setup['user1']['token'], 1)
        

def test_not_owner(setup):
#The authorised user is not an owner
    with pytest.raises(AccessError):
        admin_user_remove_v1(setup['user2']['token'], 1)

def test_remove(setup):
#remove a user and change his message to 'Removed user'
    channel_join_v1(setup['user1']['token'], setup['channels'])
    details = channel_messages_v1(setup['user2']['token'], setup['channels'], 0)
    assert details['messages'][0]['message'] == 'hello'
    admin_user_remove_v1(setup['user1']['token'], 2)
    profile = user_profile_v2(setup['user1']['token'], setup['user2']['auth_user_id']).get('user')
    assert profile['name_first'] == 'Removed'
    assert profile['name_last'] == 'user'
    details = channel_messages_v1(setup['user1']['token'], setup['channels'], 0)
    assert details['messages'][0]['message'] == 'Removed user'
