import pytest

from src.auth import auth_register_v1
from src.other import clear_v1
from src.channels import channels_create_v1
from src.channel import channel_messages_v1, channel_invite_v1
from src.message import message_send_v1
from src.error import InputError, AccessError
from src.dm import dm_create_v1
from src.search import search_v2

@pytest.fixture()
def setup():
    clear_v1()
    #Create 3 users
    user1 = auth_register_v1('apple@com.au', 'password1', 'Steve', 'Jobs')
    user2 = auth_register_v1('banana@com.au', 'password2', 'Steven', 'Jacobs')
    user3 = auth_register_v1('mango@com.au', 'password3', 'Thomas', 'Black')
    #user2 create a channel
    channel = channels_create_v1(user2['token'], 'channel', True)

    #Invite user3 to the channel
    channel_invite_v1(user2['token'], channel, 3)

    #user2 create a dm with user1 and user3 in
    dm2 = dm_create_v1(user2['token'], [1, 3])

    #user2 send some messages to channel and dm2
    message_send_v1(user2['token'], channel, 'hello', True)
    message_send_v1(user2['token'], channel, 'Today is hot', True)
    message_send_v1(user2['token'], dm2['dm_id'], 'Good morning', False)
    message_send_v1(user1['token'], dm2['dm_id'], 'God bless you', False)

    return{
        'token1': user1['token'], 
        'token2': user2['token'], 
        'token3': user3['token'],
        'channels': channel, 
        'dms': dm2['dm_id'],
    }

def test_invalid_token():
#Token passed is a invalid id
    with pytest.raises(AccessError):
        invalid_token1 = 'eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJzZXNzaW9uc19pZCI6MX0.VRz789P4O1iWpmqlZupD25REjznk5kB1ICLnPnQaTdI'
        search_v2(invalid_token1, 'pet')

def test_invalid_query_str(setup):
#query_str is invalid
    with pytest.raises(InputError):
        long_str = 'Good evening' * 100
        search_v2(setup['token1'], long_str) 

def test_search(setup):
#Search for messages
    assert search_v2(setup['token3'], 'o') == ['Today is hot', 'hello', 'God bless you', 'Good morning']
    assert search_v2(setup['token1'], 'Good') == ['Good morning']
    assert search_v2(setup['token2'], 'i') == ['Today is hot', 'Good morning']
