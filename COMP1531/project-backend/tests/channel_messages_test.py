import pytest

from src.auth import auth_register_v1
from src.channel import channel_messages_v1
from src.channels import channels_create_v1, channels_list_v1
from src.message import message_send_v1
from src.error import InputError, AccessError
from src.other import clear_v1
import time
# Create fixtures

@pytest.fixture
def setup():
    '''
    Initialises internal data of application and creates two users, one private channel
    and one public channel.
    '''
    clear_v1()
    user1 = auth_register_v1('apple@com.au', 'password1', 'Steve', 'Jobs')
    user2 = auth_register_v1('banana@com.au', 'password2', 'Steven', 'Jacobs')
    channel1 = channels_create_v1(user1['token'], 'channel1', False)
    time.sleep(0.001) # interval for helper.uniqid generation
    channel2 = channels_create_v1(user1['token'], 'channel2', True)
    return {
        'sample_user1' : user1['token'],
        'sample_user2' : user2['token'], 
        'private_channel' : channel1,
        'public_channel' : channel2,
    }

# Test channel_messages_v1
def test_user_invalid(setup):
    '''
    Tests for AccessError exception given an invalid auth_user_id.
    '''
    invalid_token1 = 'eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJzZXNzaW9uc19pZCI6MX0.VRz789P4O1iWpmqlZupD25REjznk5kB1ICLnPnQaTdI'
    with pytest.raises(AccessError):
        # User does not exist
        assert channel_messages_v1(invalid_token1, setup['public_channel'], 0)


def test_channel_invalid(setup):
    '''
    Tests for InputError exception given an invalid channel_id.
    '''
    with pytest.raises(InputError):
        # Channel -1 do not exist
        assert channel_messages_v1(setup['sample_user1'], -1, 0)
    with pytest.raises(InputError):
        # Channel 10 does not exist
        assert channel_messages_v1(setup['sample_user1'], 10, 0)

def test_channel_no_join_permissions(setup):
    '''
    Tests for AccessError exception if unauthorised user sends message from
    a channel.
    '''
    with pytest.raises(AccessError):
        # Sample User 2 is not a member of private channel
        assert channel_messages_v1(setup['sample_user2'], setup['private_channel'], 0)

def test_channel_messages_invalid_start(setup):
    '''
    Tests for InputError exception if start value is negative or greater than
    total number of channel messages.
    '''
    # No messages currently in the channel
    with pytest.raises(InputError):
        # start is greater than the total number of messages in the channel
        assert channel_messages_v1(setup['sample_user1'], setup['private_channel'], 10)
    with pytest.raises(InputError):
        # start < 0
        assert channel_messages_v1(setup['sample_user1'], setup['private_channel'], -10)

def test_channel_messages_end_index(setup):
    '''
    Tests for change in end index to ensure that -1 is returned after oldest
    messages have been returned.
    '''
    # Send 120 messages to private channel and check end index
    i = 0
    while i < 120:
        assert message_send_v1(setup['sample_user1'], setup['private_channel'], 'Hello', True)
        i += 1

    ret = channel_messages_v1(setup['sample_user1'], setup['private_channel'], 0)
    assert ret['start'] == 0 and ret['end'] == 50
    ret = channel_messages_v1(setup['sample_user1'], setup['private_channel'], 50)
    assert ret['start'] == 50 and ret['end'] == 100
    ret = channel_messages_v1(setup['sample_user1'], setup['private_channel'], 100)
    assert ret['start'] == 100 and ret['end'] == -1
