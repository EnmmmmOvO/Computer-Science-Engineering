'''
Channel features
'''
from src.data import users, channels
from src.channels import channels_list_v1
from src.error import InputError, AccessError
from src.other import notify
import src.helper as helper

def channel_invite_v1(token, channel_id, u_id):
    """Invites a user (with user id u_id) to join a channel with ID channel_id. 
    Once invited the user is added to the channel immediately

    Arguments:
        token (integer): unique user token
        channel_id (integer): id of channel that the user will be invited in
        u_id: id of user to be invited

    Exceptions:
        AccessError:
            - token does not exist or is invalid
            - auth_user_id is not a member of channel with channel_id
        InputError: 
            - channel_id does not refer to a valid channel 
            - u_id does not refer to a valid user

    Return Value:
        dict: void dict
    """

    token_decoded = helper.check_token(token)

    # Input check
    helper.channel_check(channel_id)
    helper.user_check(u_id)

    # Access check
    helper.token_check(token)
    authorised_u_ids = [member['u_id'] for member in channels[channel_id]['all_members']]
    if token_decoded['auth_user_id'] not in authorised_u_ids:
        raise AccessError(description='Invalid User: User is not in channel list')

    # If not already a member, add user info of u_id
    if u_id not in authorised_u_ids:
        user_info = helper.user_info(u_id)
        channels[channel_id]['all_members'].append(user_info)
        if users[u_id]['permission_id'] == 1:
            channels[channel_id]['owner_members'].append(user_info)
        notify(token_decoded['auth_user_id'], u_id, channel_id, -1, "", False)

    return {}


def channel_details_v1(token, channel_id):
    """Given a Channel with ID channel_id that the authorised user is part of, 
    provide basic details about the channel

    Arguments:
        token (integer): unique user token
        channel_id (integer): id of channel of interest

    Exceptions:
        AccessError:
            - token does not exist or is invalid
            - auth_user_id is not a member of channel with channel_id
        InputError:
            - channel_id does not refer to a valid channel

    Return Value:
        dict: details of channel with channel_id
    """

    token_decoded = helper.check_token(token)

    # Input check
    helper.channel_check(channel_id)

    # Access check
    helper.token_check(token)
    helper.user_in_channel_check(token_decoded['auth_user_id'], channel_id)

    # Access details of channel with channel_id
    return {
        'name': channels[channel_id]['name'],
        'is_public' : channels[channel_id]['public'],
        'owner_members': channels[channel_id]['owner_members'],
        'all_members': channels[channel_id]['all_members'],
    }


def channel_messages_v1(token, channel_id, start):
    '''
    Given a valid channel_id for an authorised user, returns up to 50 messages
    between index 'start' and 'start + 50'.

    Arguments:
        token <bytes> - unique user token
        channel_id <int> - unique channel id
        start <int> - index for message number

    Exceptions:
        InputError  - Occurs when channel does not exist or when start value is negative
		      or greater than number of messages in the specified channel
        AccessError - Occurs when user does not exist or user is not in channel
                      list.

    Return Value:
        Returns a dictionary consisting of a list of 'messages' (less than 50)
	    as well as 'start' and 'end' values. Returns start + 50 in end
        value if not all messages have loaded. Returns -1 in end if oldest messages
	    have been loaded.
    '''

    # Check for valid token 
    helper.token_check(token)
    # Check if channel exists
    helper.channel_check(channel_id)

    # Check if user is in channel 
    channel_info = helper.channel_info(channel_id)

    if channel_info not in channels_list_v1(token):
        raise AccessError(description='Invalid User: User is not in channel list')

    message_list = [message for message in channels[channel_id]['messages']]
    if start < 0 or start > len(message_list):
        raise InputError(description='Invalid Index Value: Message index does not exist')

    # Assuming 0 < start < len(message_list)
    if len(message_list[start:]) < 50:
        end = -1
    else:
        end = start + 50

    return {
        'messages': message_list[start:] if end == -1 else message_list[start:end],
        'start': start,
        'end': end,
    }

def channel_leave_v1(token, channel_id):
    '''
    Given a channel ID, the user removed as a member of this channel. Their messages should remain in the channel

    Arguments:
        token <bytes> - unique user token
        channel_id <int> - unique channel id

    Exceptions:
        InputError  - Occurs when channel ID is not a valid channel
        AccessError - Occurs when authorised user is not a member of channel with channel_id

    Return Value:
        dict: void dict
    '''

    token_decoded = helper.check_token(token)

    # Check for valid token 
    helper.token_check(token)
    # Check if channel exists
    helper.channel_check(channel_id)

    # Check if user is in channel
    helper.token_check(token)
    helper.user_check(token_decoded['auth_user_id'])
    helper.user_in_channel_check(token_decoded['auth_user_id'], channel_id)
    
    user_info = helper.user_info(token_decoded['auth_user_id'])

    # Delete user info from owner members if user is an owner
    if user_info in channels[channel_id]['owner_members']:
        idx1 = channels[channel_id]['owner_members'].index(user_info)
        del channels[channel_id]['owner_members'][idx1]
    
    idx2 = channels[channel_id]['all_members'].index(user_info)
    del channels[channel_id]['all_members'][idx2]

    return {}

def channel_join_v1(token, channel_id):
    '''
    Given a channel_id of a channel that the authorised user can join,
    adds them to that channel.

    Arguments:
        token <bytes> - unique user token
        channel_id <int> - unique channel id

    Exceptions:
        InputError  - Occurs when channel does not exist.
        AccessError - Occurs when user does not exist or user is not in channel
                      list.

    Return Value:
        dict: void dict
    '''

    token_decoded = helper.check_token(token)

    helper.token_check(token)
    helper.channel_check(channel_id)

    member_info = helper.user_info(token_decoded['auth_user_id'])
    
    # If channel is a public channel
    if channels[channel_id]['public']:
        channels[channel_id]['all_members'].append(member_info)
    # user is a global owner
    elif users[token_decoded['auth_user_id']]['permission_id'] == 1:
        channels[channel_id]['owner_members'].append(member_info)
        channels[channel_id]['all_members'].append(member_info)
    # not a global owner and accessing a private channel
    else:
        raise AccessError(description='Private Channel: User cannot join this channel')
    
    return {}

def channel_addowner_v1(token, channel_id, u_id):
    '''
    Make user with user id u_id an owner of this channel.

    Arguments:
        token <bytes> - unique user token
        channel_id <int> - unique channel id
        u_id <int> - id of user to be added

    Exceptions:
        InputError  - Occurs when channel does not exist and when user with 
                      user id u_id is already an owner of the channel.
        AccessError - when the authorised user is not an owner of the **Dreams**, 
                      or an owner of this channel

    Return Value:
        dict: void dict
    '''

    token_decoded = helper.check_token(token)
    helper.token_check(token)

    auth_user_id = token_decoded['auth_user_id']
    helper.user_check(auth_user_id)
    helper.channel_check(channel_id)

    helper.user_own_channel_check(auth_user_id, channel_id)
    helper.user_check(u_id)
    user_info = helper.user_info(u_id)

    member_list = [members['u_id'] for members in channels[channel_id]['all_members']]
    
    if user_info in channels[channel_id]['owner_members']:
        raise InputError(description='User already an owner')
    
    if u_id not in member_list:
        notify(token_decoded['auth_user_id'], u_id, channel_id, -1, "", False)
        channels[channel_id]['all_members'].append(user_info)

    channels[channel_id]['owner_members'].append(user_info)

    return {}

def channel_removeowner_v1(token, channel_id, u_id):
    '''
    Remove user with user id u_id an owner of this channel

    Arguments:
        token <bytes> - unique user token
        channel_id <int> - unique channel id
        u_id <int> - id of user to be removed

    Exceptions:
        InputError  - Occurs when channel does not exist.
        AccessError - Occurs when user does not exist or user is not in channel
                      list.

    Return Value:
        dict: void dict
    '''
    token_decoded = helper.check_token(token)
    helper.token_check(token)

    auth_user_id = token_decoded['auth_user_id']
    helper.user_check(auth_user_id)
    helper.channel_check(channel_id)

    helper.user_own_channel_check(auth_user_id, channel_id)
    helper.user_check(u_id)

    user_info = helper.user_info(u_id)    
    if user_info not in channels[channel_id]['owner_members']:
        raise InputError(description='User already not an owner')
    if len(channels[channel_id]['owner_members']) == 1:
        raise InputError(description='User is the only owner')

    idx = channels[channel_id]['owner_members'].index(user_info)

    del channels[channel_id]['owner_members'][idx]
    return {}

