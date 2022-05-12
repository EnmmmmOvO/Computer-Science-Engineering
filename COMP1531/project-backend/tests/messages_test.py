import pytest
import jwt
from datetime import datetime, timezone
from time import sleep
# from src.data import users, channels, alltime_total_sys_messages
from src.auth import auth_register_v1
from src.channel import channel_messages_v1, channel_addowner_v1, channel_invite_v1
from src.channels import channels_create_v1
from src.dm import dm_create_v1, dm_messages_v1
from src.message import message_send_v1, message_edit_v1, \
                        message_remove_v1, message_share_v1, message_send_later_v1, \
                        message_pin_unpin_v1
from src.error import InputError, AccessError
from src.other import clear_v1
import src.helper as helper
# Create fixtures

@pytest.fixture
def setup():
    '''
    Initialises internal data of application and creates two users, two private channels
    and one public channel.
    '''
    clear_v1()
    user1 = auth_register_v1('apple@com.au', 'password1', 'Steve', 'Jobs')
    user2 = auth_register_v1('banana@com.au', 'password2', 'Steven', 'Jacobs')
    user3 = auth_register_v1('cabana@com.au', 'password3', 'Stephen', 'Jacobes')
    channel1 = channels_create_v1(user1['token'], 'channel1', False)
    channel2 = channels_create_v1(user1['token'], 'channel2', True)
    channel3 = channels_create_v1(user2['token'], 'channel3', False)
    dm1 = dm_create_v1(user1['token'], [user2['auth_user_id']])
    dm2 = dm_create_v1(user1['token'], [user3['auth_user_id']])

    return {
        'sample_user1' : user1['token'],
        'sample_user2' : user2['token'], 
        'sample_user3' : user3,
        'private_channel' : channel1,
        'public_channel' : channel2,
        'private_channel2' : channel3,
        'dm1' : dm1['dm_id'],
        'dm2' : dm2['dm_id'],
    }


'''
Tests for message_send_v1, message_edit_v1, message_remove_v1
'''

def test_user_invalid(setup):
    '''
    Tests for AccessError exception given an invalid auth_user_id.
    '''
    u1_payload = jwt.decode(setup['sample_user1'], 'This is a very safe secret', \
                            algorithms=["HS256"])
    invalid_token1 = jwt.encode(u1_payload, "I don't know but I want to hack", \
                                algorithm = 'HS256')
    with pytest.raises(AccessError):
        # User does not exist
        assert message_send_v1(invalid_token1, setup['public_channel'], 'Hello', True)

    msg_id = message_send_v1(setup['sample_user1'], setup['private_channel'], 'Hello', True)
    with pytest.raises(AccessError):
        # User does not exist
        assert message_edit_v1(invalid_token1, msg_id, 'World')
    
    with pytest.raises(AccessError):
        # User does not exist
        assert message_remove_v1(invalid_token1, msg_id)
    
    with pytest.raises(AccessError):
        # User does not exist
        assert message_share_v1(invalid_token1, msg_id, '', setup['public_channel'], -1)

def test_channel_dm_invalid(setup):
    '''
    Tests for InputError exception given an invalid channel_id/dm_id.
    '''
    with pytest.raises(InputError):
        # Channel -1 does not exist
        assert message_send_v1(setup['sample_user1'], -1, 'Hello', True)
    with pytest.raises(InputError):
        # DM -1 does not exist
        assert message_send_v1(setup['sample_user3']['token'], -1, 'Hello', False)

def test_channel_no_join_permissions(setup):
    '''
    Tests for AccessError exception if unauthorised user tries to post message
    from a channel/dm.
    '''
    with pytest.raises(AccessError):
        # Sample User 2 is not a member of private channel
        assert message_send_v1(setup['sample_user2'], setup['private_channel'], "Hello", True)
    with pytest.raises(AccessError):
        # Sample User 2 is not a member of dm1
        assert message_send_v1(setup['sample_user3']['token'], setup['dm1'], 0, False)

def test_message_edit_remove_share_unauthorised(setup):
    # User 1 sends message to private channel 1
    msg_id1 = message_send_v1(setup['sample_user1'], setup['private_channel'], 'Hello World 1', True)
    msg_id2 = message_send_v1(setup['sample_user1'], setup['dm2'], "Hello World 2", False)
    # User 1 can edit message with msg_id
    assert message_edit_v1(setup['sample_user1'], msg_id1, 'Goodbye World 1') == {}
    assert message_edit_v1(setup['sample_user1'], msg_id2, 'Goodbye World 2') == {}
    with pytest.raises(AccessError):
        # User 2 did not send message
        message_edit_v1(setup['sample_user2'], msg_id1, 'Goodbye')
    with pytest.raises(AccessError):
        # User 3 did not send message
        assert message_edit_v1(setup['sample_user3']['token'], msg_id2, "Goodbye")
    with pytest.raises(AccessError):
        # User 2 did not send message
        message_remove_v1(setup['sample_user2'], msg_id1)
    with pytest.raises(AccessError):
        # User 3 did not send message
        message_remove_v1(setup['sample_user3']['token'], msg_id2)
    with pytest.raises(AccessError):
        # User 1 has not joined Private Channel 2 (Name : Channel 3)
        message_share_v1(setup['sample_user1'], msg_id1, '', \
                            setup['private_channel2'], -1)
    with pytest.raises(AccessError):
        # User 2 has not joined DM2
        message_share_v1(setup['sample_user2'], msg_id2, '', -1, setup['dm2'])

def test_global_owner_message_edit_remove(setup):
    msg_id1 = message_send_v1(setup['sample_user2'], setup['private_channel2'], \
                                'Hello It\'s me', True)
    msg_id2 = message_send_v1(setup['sample_user2'], setup['private_channel2'], \
                                'Hello It is me', True)
    msg_id3 = message_send_v1(setup['sample_user2'], setup['dm1'], 'Hello It\'s me', \
                                False)
    msg_id4 = message_send_v1(setup['sample_user2'], setup['dm1'], 'Hello It is me', \
                                False)

    # Channel Owner Member deletes msg_id1-msg_id2 in two different ways
    channel_addowner_v1(setup['sample_user2'], setup['private_channel2'], \
                        setup['sample_user3']['auth_user_id'])
    message_edit_v1(setup['sample_user3']['token'], msg_id1, '')
    message_remove_v1(setup['sample_user3']['token'], msg_id2)
    # Global Owner deletes msg_id3-msg_id4 in two different ways
    message_edit_v1(setup['sample_user1'], msg_id3, '')
    message_remove_v1(setup['sample_user1'], msg_id4)

    with pytest.raises(InputError):
        # Message ID refers to a deleted message
        message_edit_v1(setup['sample_user2'], msg_id1, 'Goodbye')
    with pytest.raises(InputError):
        # Message ID refers to a deleted message
        message_remove_v1(setup['sample_user2'], msg_id2)
    with pytest.raises(InputError):
        # Message ID refers to a deleted message
        message_edit_v1(setup['sample_user2'], msg_id3, 'Goodbye')
    with pytest.raises(InputError):
        # Message ID refers to a deleted message
        message_remove_v1(setup['sample_user2'], msg_id4)

def test_message_send_and_edit_too_big(setup):
    '''
    Tests for InputError exception if message length exceeds 1000 characters or is 0.
    '''
    message = "Sed ut perspiciatis unde omnis iste natus error sit voluptatem" * 1000

    # Test message greater than 1000 characters and empty string
    with pytest.raises(InputError):
        assert message_send_v1(setup['sample_user1'], setup['private_channel'], \
                                message, True)
    with pytest.raises(InputError):
        assert message_send_v1(setup['sample_user1'], setup['private_channel'], \
                                 "", True)

    future_time = int(datetime.now().replace(tzinfo=timezone.utc).timestamp()) + 10

    with pytest.raises(InputError):
        assert message_send_later_v1(setup['sample_user1'], setup['private_channel'], \
                                message, True, future_time)
    with pytest.raises(InputError):
        assert message_send_later_v1(setup['sample_user1'], setup['private_channel'], \
                                 "", True, future_time)

    with pytest.raises(InputError):
        assert message_send_v1(setup['sample_user1'], setup['dm1'], message, False)
    with pytest.raises(InputError):
        assert message_send_v1(setup['sample_user1'], setup['dm1'], "", False)
    
    with pytest.raises(InputError):
        assert message_send_later_v1(setup['sample_user1'], setup['dm1'], message, False, future_time)
    with pytest.raises(InputError):
        assert message_send_later_v1(setup['sample_user1'], setup['dm1'], "", False, future_time)

    msg_id1 = message_send_v1(setup['sample_user1'], setup['private_channel'], \
                                'Hello', True)
    msg_id2 = message_send_v1(setup['sample_user1'], setup['dm1'], 'Hello', False)
    
    # Edit msg_id1 and msg_id2 with a message that exceeds 1000 characters
    with pytest.raises(InputError):
        assert message_edit_v1(setup['sample_user1'], msg_id1, message)
    with pytest.raises(InputError):
        assert message_edit_v1(setup['sample_user1'], msg_id2, message)

'''
Tests for message_share_v1
'''

def test_message_share(setup):
    # User 1 sends message to private channel 1 and dm1
    msg_id1 = message_send_v1(setup['sample_user1'], setup['private_channel'], \
                                'Hello World', True)
    msg_id2 = message_send_v1(setup['sample_user1'], setup['dm1'], 'Hello World', \
                                False)
    
    ch_msgs = channel_messages_v1(setup['sample_user1'], setup['private_channel'], 0).get('messages')
    dm_msgs = dm_messages_v1(setup['sample_user1'], setup['dm1'], 0).get('messages')

    assert msg_id1 in [ch_msgs[idx]['message_id'] for idx in range(len(ch_msgs))]
    assert msg_id2 in [dm_msgs[idx]['message_id'] for idx in range(len(dm_msgs))]

    # User 1 shares msg_id1 to public channel and msg_id2 to dm2
    assert message_share_v1(setup['sample_user1'], msg_id1, \
                        'I come from another planet', setup['public_channel'], -1)
    assert message_share_v1(setup['sample_user1'], msg_id2, \
                        'What is the meaning of this monstrosity', -1, setup['dm2'])

    # Check that a new message has been added to public channel and dm2
    assert len(channel_messages_v1(setup['sample_user1'], setup['public_channel'], 0).get('messages')) == 1
    assert len(dm_messages_v1(setup['sample_user1'], setup['dm2'], 0).get('messages')) == 1


'''
Tests for message_pin_unpin_v1
'''

def test_message_pin_unpin_twice_channel(setup):
    # User 1 sends message to private channel 1
    msg_id = message_send_v1(setup['sample_user1'], setup['private_channel'], \
                                'Hello World', True)
    # User 1 pins msg_id
    assert message_pin_unpin_v1(setup['sample_user1'], msg_id, True) == {}

    # User 1 pins msg_id again
    with pytest.raises(InputError):
        message_pin_unpin_v1(setup['sample_user1'], msg_id, True)
    
    # User 1 unpins msg_id
    assert message_pin_unpin_v1(setup['sample_user1'], msg_id, False) == {}

    # User 1 unpins msg_id again
    with pytest.raises(InputError):
        message_pin_unpin_v1(setup['sample_user1'], msg_id, False)

def test_message_pin_unpin_twice_dm(setup):
    # User 1 sends message to dm1
    msg_id = message_send_v1(setup['sample_user1'], setup['dm1'], \
                                'Hello World', False)
    # User 1 pins msg_id
    assert message_pin_unpin_v1(setup['sample_user1'], msg_id, True) == {}

    # User 1 pins msg_id again
    with pytest.raises(InputError):
        message_pin_unpin_v1(setup['sample_user1'], msg_id, True)
    
    # User 1 unpins msg_id
    assert message_pin_unpin_v1(setup['sample_user1'], msg_id, False) == {}

    # User 1 unpins msg_id again
    with pytest.raises(InputError):
        message_pin_unpin_v1(setup['sample_user1'], msg_id, False)

def test_message_pin_unpin_invalid(setup):
    # Create an invalid message_id
    invalid_msg_id = message_send_v1(setup['sample_user1'], setup['private_channel'], \
                                'Hello World', True) + 1

    with pytest.raises(InputError):
        message_pin_unpin_v1(setup['sample_user1'], invalid_msg_id, True)

def test_message_pin_unpin_unauthorised_channel(setup):
    # User 1 sends message to private channel 1
    msg_id1 = message_send_v1(setup['sample_user1'], setup['private_channel'], \
                                'Hello World', True)
                                
    # User 3 tries to pin msg_id1 (not in channel)
    with pytest.raises(AccessError):
        message_pin_unpin_v1(setup['sample_user3']['token'], msg_id1, True)

    channel_invite_v1(setup['sample_user1'], setup['private_channel'], \
                        setup['sample_user3']['auth_user_id'])

    # User 3 tries to pin msg_id1 (not an owner)
    with pytest.raises(AccessError):
        message_pin_unpin_v1(setup['sample_user3']['token'], msg_id1, True)

    # User pins the message
    message_pin_unpin_v1(setup['sample_user1'], msg_id1, True)

    # User 3 tries to unpin msg_id1 (not an owner)
    with pytest.raises(AccessError):
        message_pin_unpin_v1(setup['sample_user3']['token'], msg_id1, False)

def test_message_pin_unpin_unauthorised_dm(setup):
    # User 1 sends message to dm1
    msg_id1 = message_send_v1(setup['sample_user1'], setup['dm1'], \
                                'Hello World', False)
                                
    # User 3 tries to pin msg_id1 (not a dm owner)
    with pytest.raises(AccessError):
        message_pin_unpin_v1(setup['sample_user3']['token'], msg_id1, True)

    # User 1 pins the message
    message_pin_unpin_v1(setup['sample_user1'], msg_id1, True)

    # User 3 tries to unpin msg_id1 (not an owner)
    with pytest.raises(AccessError):
        message_pin_unpin_v1(setup['sample_user3']['token'], msg_id1, False)

def test_message_pin_unpin(setup):
    # User 1 sends message to private channel 1 and dm1
    msg_id1 = message_send_v1(setup['sample_user1'], setup['private_channel'], \
                                'Hello World', True)
    msg_id2 = message_send_v1(setup['sample_user1'], setup['dm1'], 'Hello World', \
                                False)

    # User 1 pins and unpins messages
    assert message_pin_unpin_v1(setup['sample_user1'], msg_id1, True) == {}
    assert message_pin_unpin_v1(setup['sample_user1'], msg_id2, True) == {}
    assert message_pin_unpin_v1(setup['sample_user1'], msg_id1, False) == {}
    assert message_pin_unpin_v1(setup['sample_user1'], msg_id2, False) == {}

    channel_addowner_v1(setup['sample_user1'], setup['private_channel'], \
                    setup['sample_user3']['auth_user_id'])

    # User 3 pins message again
    assert message_pin_unpin_v1(setup['sample_user3']['token'], msg_id1, True) == {}
    assert message_pin_unpin_v1(setup['sample_user3']['token'], msg_id1, False) == {}


'''
Tests for message_send_later_v1
'''

def test_message_send_past(setup):
    past_time = int(datetime.now().replace(tzinfo=timezone.utc).timestamp()) - 10
    
    with pytest.raises(InputError):
        message_send_later_v1(setup['sample_user1'], setup['private_channel'], \
                                'Hello World', True, past_time)
    with pytest.raises(InputError):
        message_send_later_v1(setup['sample_user1'], setup['private_channel'], \
                                'Hello World', False, past_time)

def test_message_send_later(setup):
    future_time = int(datetime.now().replace(tzinfo=timezone.utc).timestamp()) + 10
    # User 1 sends message to private channel 1 and dm1
    message_send_later_v1(setup['sample_user1'], setup['private_channel'], \
                                'Hello World', True, future_time)
    message_send_later_v1(setup['sample_user1'], setup['dm1'], 'Hello World', \
                                False, future_time)
    
    assert len(channel_messages_v1(setup['sample_user1'], setup['private_channel'], 0).get('messages')) == 0
    assert len(dm_messages_v1(setup['sample_user1'], setup['dm1'], 0).get('messages')) == 0

    # Wait 10s
    sleep(10)
    
    assert len(channel_messages_v1(setup['sample_user1'], setup['private_channel'], 0).get('messages')) == 1
    assert len(dm_messages_v1(setup['sample_user1'], setup['dm1'], 0).get('messages')) == 1
