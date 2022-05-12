import pytest

from src.auth import auth_register_v1
from src.channel import channel_invite_v1, channel_addowner_v1
from src.channels import channels_create_v1
from src.dm import dm_create_v1, dm_invite_v1
from src.message import message_send_v1, message_edit_v1
from src.other import clear_v1, get_notifications_v1
from src.error import AccessError

@pytest.fixture
def setup():
    '''
    Initialises internal data of application and creates two users and two 
    channels (one public and one private).
    '''
    clear_v1()
    user1 = auth_register_v1('apple@com.au', 'password1', 'Steve', 'Jobs')
    user2 = auth_register_v1('banana@com.au', 'password2', 'Steven', 'Jacobs')
    user3 = auth_register_v1('cabana@com.au', 'password3', 'Stephen', 'Jacobes')
    channel1 = channels_create_v1(user1['token'], 'channel1', False)
    channel2 = channels_create_v1(user1['token'], 'channel2', True)
    dm1 = dm_create_v1(user1['token'], [user3['auth_user_id']])
    return {
        'sample_user1' : user1,
        'sample_user2' : user2, 
        'sample_user3' : user3,
        'private_channel' : channel1,
        'public_channel' : channel2,
        'dm1' : dm1['dm_id'],
    }

def test_invalid_token():
    '''
    Tests for AccessError exception given an invalid auth_user_id.
    '''
    invalid_token1 = 'eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJzZXNzaW9uc19pZCI6MX0.VRz789P4O1iWpmqlZupD25REjznk5kB1ICLnPnQaTdI'
    with pytest.raises(AccessError):
        # User does not exist
        assert get_notifications_v1(invalid_token1)

def test_notifications(setup):
    '''
    Tests for message tag notifications for channels/dms and channel/dm invitation.
    '''

    # User 1 invites User 2 to public channel
    channel_invite_v1(setup['sample_user1']['token'], setup['public_channel'], setup['sample_user2']['auth_user_id'])
    assert len(get_notifications_v1(setup['sample_user2']['token'])) == 1
    
    # User 1 sends a message to the public channel, tagging User 2 by handle (thereby sending a notification)
    msg_id1 = message_send_v1(setup['sample_user1']['token'], setup['public_channel'], "@stevenjacobs How are you?", True)
    assert len(get_notifications_v1(setup['sample_user2']['token'])) == 2
    message_edit_v1(setup['sample_user1']['token'], msg_id1, "@stevenjacobs Please reply")
    assert len(get_notifications_v1(setup['sample_user2']['token'])) == 3
    
    # User 1 invites User 2 to dm1
    dm_invite_v1(setup['sample_user1']['token'], setup['dm1'], setup['sample_user2']['auth_user_id'])
    assert len(get_notifications_v1(setup['sample_user2']['token'])) == 4
    
    # User 1 sends a message to the dm1, tagging User 2 by handle (thereby sending a notification)
    # First tag does not work since handle is incorrect
    msg_id1 = message_send_v1(setup['sample_user1']['token'], setup['dm1'], "@stevenjacobss Reply to the channel", False)
    assert len(get_notifications_v1(setup['sample_user2']['token'])) == 4
    message_edit_v1(setup['sample_user1']['token'], msg_id1, "@stevenjacobs Are you alive")
    assert len(get_notifications_v1(setup['sample_user2']['token'])) == 5

def test_add_thru_ch_addowner_triggers_notification(setup):
    # User 1 adds User 2 as owner to Public Channel
    channel_addowner_v1(setup['sample_user1']['token'], setup['public_channel'], setup['sample_user2']['auth_user_id'])
    
    assert len(get_notifications_v1(setup['sample_user2']['token'])) == 1

def test_add_thru_dm_create_triggers_notification(setup):
    # User 3 was added in DM1 in setup
    assert len(get_notifications_v1(setup['sample_user3']['token'])) == 1