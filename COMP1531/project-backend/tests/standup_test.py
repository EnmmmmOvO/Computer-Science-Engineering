'''
Tests for standup start, active, send
'''
import pytest
import asyncio
from src.standup import standup_start_v1, standup_active_v1, standup_send_v1
from src.error import InputError, AccessError
from src.channel import channel_messages_v1
from src.data import channels
from src.auth import auth_register_v1, generate_token
from src.channels import channels_create_v1
from src.channel import channel_invite_v1
from src.other import clear_v1
import time

@pytest.fixture
def setup():
    clear_v1()
    user1 = auth_register_v1('apple@com.au', 'password1', 'Steve', 'Jobs')
    user2 = auth_register_v1('banana@com.au', 'password2', 'Steven', 'Jacobs')
    user3 = auth_register_v1('cherry@com.au', 'password3', 'Sarah', 'Jane')
    user4 = auth_register_v1('durian@com.au', 'password4', 'Sam', 'Jonh')
    sample_channel_id1 = channels_create_v1(user1['token'], 'Group 1', True)
    time.sleep(0.001)
    sample_channel_id2 = channels_create_v1(user4['token'], 'Group 2', True)
    channel_invite_v1(user1['token'], sample_channel_id1, user2['auth_user_id'])
    channel_invite_v1(user1['token'], sample_channel_id1, user3['auth_user_id'])
    
    return {
        'sample_user1': user1,
        'sample_user2': user2,
        'sample_user3': user3,
        'sample_user4': user4,
        'sample_channel_id1': sample_channel_id1,
        'sample_channel_id2': sample_channel_id2
    }


def test_standup_start_v1(setup):
    assert standup_start_v1(setup['sample_user1']['token'], setup['sample_channel_id1'], 0.001)['time_finished']
    time.sleep(0.1)


def test_standup_start_v1_except(setup):
    # when any of authorised user is not in the channel
    with pytest.raises(AccessError):
        standup_start_v1(setup['sample_user4']['token'], setup['sample_channel_id2'], 0.001)

    with pytest.raises(InputError):
        # channel ID is not a valid channel
        standup_start_v1(setup['sample_user4']['token'], -1, 0.001)
        # an active standup is currently running in this channel
        if not standup_active_v1(setup['sample_user1']['token'], setup['sample_channel_id1'])['is_active']:
            standup_start_v1(setup['sample_user1']['token'], setup['sample_channel_id1'], 0.001)
        standup_start_v1(setup['sample_user1']['token'], setup['sample_channel_id1'], 0.001)
        time.sleep(0.001)

def test_standup_active_v1(setup):
    assert standup_active_v1(setup['sample_user1']['token'], setup['sample_channel_id1'])['is_active'] == False
    standup_start_v1(setup['sample_user1']['token'], setup['sample_channel_id1'], 0.001)
    # wait for start
    assert standup_active_v1(setup['sample_user1']['token'], setup['sample_channel_id1'])['is_active'] == True
    # wait for finishing task
    time.sleep(0.1)
    assert standup_active_v1(setup['sample_user1']['token'], setup['sample_channel_id1'])['is_active'] == False


def test_standup_active_v1_except(setup):
    with pytest.raises(InputError):
        # channel ID is not a valid channel
        standup_active_v1(setup['sample_user1']['token'], -1)


def test_standup_send_v1(setup):
    message_str = 'this is a message from sample user 1'
    standup_start_v1(setup['sample_user1']['token'], setup['sample_channel_id1'], 0.001)
    # wait for start
    assert standup_send_v1(setup['sample_user1']['token'], setup['sample_channel_id1'], message_str) == {}
    # wait for finishing task
    time.sleep(0.1)
    answer = channel_messages_v1(setup['sample_user1']['token'], setup['sample_channel_id1'], 0)['messages']
    answer = [ans['message'] for ans in answer]
    assert answer == [message_str]


def test_standup_send_v1_except(setup):
    message_str = 'this is a message from sample user 1'
    with pytest.raises(AccessError):
        # - the authorised user is not a member of the channel that the message is within
        standup_send_v1(setup['sample_user4']['token'], setup['sample_channel_id1'], message_str)
    with pytest.raises(InputError):
        # - channel ID is not a valid channel
        standup_send_v1(setup['sample_user1']['token'], -1, message_str)
        # - message is more than 1000 characters (not including the username and colon)
        standup_send_v1(setup['sample_user4']['token'], setup['sample_channel_id1'], message_str * 50)
        # - an active standup is not currently running in this channel
        standup_send_v1(setup['sample_user1']['token'], setup['sample_channel_id1'], message_str)
