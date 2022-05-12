import asyncio
import time
import uuid
from datetime import datetime
from src.data import channels
from src.error import InputError, AccessError
import src.helper as helper
from threading import Timer

def end_standup(channel_id):
    channels[channel_id]['messages'] = channels[channel_id]['buffer'] + channels[channel_id]['messages']
    channels[channel_id]['buffer'].clear()
    channels[channel_id]['is_active'] = False
    # print(f'end standup# {channel_id} is active = ', channels[channel_id]['is_active'], time.time())

def standup_start_v1(token, channel_id, length):
    '''
    For a given channel, start the standup period whereby for the 
    next "length" seconds if someone calls "standup_send" with a 
    message, it is buffered during the X second window then at the 
    end of the X second window a message will be added to the message 
    queue in the channel from the user who started the standup. X is 
    an integer that denotes the number of seconds that the standup occurs for

    Arguments:
        token (string): unique user token
        channel_id (integer): id of the interested channel
        length (integer): number of seconds

    Exceptions:
        AccessError:
            - when any of authorised user is not in the channel
        InputError: 
            - channel ID is not a valid channel
            - an active standup is currently running in this channel

    Return Value:
        dict: { time_finish }
    '''
    global channels

    token_decoded = helper.check_token(token)
    helper.token_check(token)

    auth_user_id = token_decoded['auth_user_id']
    helper.user_check(auth_user_id)
    helper.channel_check(channel_id)
    helper.user_in_channel_check(auth_user_id, channel_id)

    if len(channels[channel_id]['all_members']) <= 1:
        raise AccessError(description='any of authorised user is not in the channel')
    if channels[channel_id]['is_active']:
        raise InputError(description='an active standup is currently running in this channel')

    channels[channel_id]['is_active'] = True
    # print(f'start# {channel_id} is active = ', channels[channel_id]['is_active'], time.time())
    t = Timer(length, end_standup, [channel_id])
    t.start()
    return {'time_finished': str(datetime.now())}


def standup_active_v1(token, channel_id):
    '''
    For a given channel, return whether a standup is active in it, 
    and what time the standup finishes. If no standup is active, 
    then time_finish returns None

    Arguments:
        token (string): unique user token
        channel_id (integer): id of the interested channel

    Exceptions:
        InputError: 
            - channel ID is not a valid channel

    Return Value:
        dict: { is_active, time_finish }
    '''

    token_decoded = helper.check_token(token)
    helper.token_check(token)

    auth_user_id = token_decoded['auth_user_id']
    helper.user_check(auth_user_id)
    helper.channel_check(channel_id)
    helper.user_in_channel_check(auth_user_id, channel_id)
    # print(f'active# {channel_id} is active = ', channels[channel_id]['is_active'])

    return {'is_active': channels[channel_id]['is_active'], 'time_finished': str(datetime.now())}


def standup_send_v1(token, channel_id, message):
    '''
    Sending a message to get buffered in the standup queue, 
    assuming a standup is currently active

    Arguments:
        token (string): unique user token
        channel_id (integer): id of the interested channel
        length (integer): number of seconds

    Exceptions:
        AccessError:
            - the authorised user is not a member of the channel that the message is within
        InputError: 
            - channel ID is not a valid channel
            - message is more than 1000 characters (not including the username and colon)
            - an active standup is not currently running in this channel

    Return Value:
        dict: {}
    '''

    token_decoded = helper.check_token(token)
    helper.token_check(token)

    auth_user_id = token_decoded['auth_user_id']
    helper.user_check(auth_user_id)
    helper.channel_check(channel_id)
    helper.user_in_channel_check(auth_user_id, channel_id)

    if len(message) > 1000 or len(message) == 0:
        raise InputError(description='Invalid Message: Message must be within 1000 characters')
    if not channels[channel_id]['is_active']:
        raise InputError(description='an active standup is not currently running in this channel')

    message_id = uuid.uuid4().int
    message_info = {
        'message_id': message_id,
        'dest_id': channel_id,
        'u_id': auth_user_id,
        'message': message,
        'time_created': str(datetime.now()),
    }
    channels[channel_id]['buffer'].insert(0, message_info)

    return {}