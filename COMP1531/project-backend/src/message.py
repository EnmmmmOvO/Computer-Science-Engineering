'''
Message features
'''
import uuid
import threading
from typing import AnyStr, Optional
from datetime import datetime, timezone
from src.data import users, channels, dms
from src.error import InputError, AccessError
import src.helper as helper
from src.other import notify

# React id
REACT = 1

# message_send_v1 is used for message/send/v1 and message/senddm/v1
def message_send_v1(token: AnyStr, ch_or_dm_id: int, message: str, to_channel: bool) -> dict:
    '''
    Sends a message from an authorised user to the channel/dm specified.

    Arguments:
        token <bytes> - unique user token
        ch_or_dm_id <int> - unique channel/dm id
        message <string> - message that is to be sent to the channel/dm
        to_channel <bool> - boolean that is True if message destination is a channel
                            and False for dms

    Exceptions:
        InputError  - Occurs when channel/dm does not exist or message length
                      is not between 1 and 1000 characters.
        AccessError - Occurs when token does not exist or user is not in channel/dm
                      list.

    Return Value:
        Returns the unique message_id for the message
    '''

    token_decoded = helper.check_token(token)

    helper.token_check(token)
    helper.channel_check(ch_or_dm_id) if (to_channel) else helper.dm_check(ch_or_dm_id)
    helper.user_in_channel_check(token_decoded['auth_user_id'], ch_or_dm_id) if (to_channel) else \
        helper.user_in_dm_check(token_decoded['auth_user_id'], ch_or_dm_id)

    if len(message) > 1000 or len(message) == 0:
        raise InputError(description='Invalid Message: Message must be within 1000 characters')

    message_id = helper.uniqid()
    
    message_info = {
        'message_id': message_id,
        'dest_id': ch_or_dm_id,
        'u_id': token_decoded['auth_user_id'],
        'message': message,
        'time_created': int(datetime.now().replace(tzinfo=timezone.utc).timestamp()) ,
        'reacts': [{
            'react_id': 1,
            'u_ids': [],
            'is_this_user_reacted': False,
        }],
        'is_pinned': False
    }

    add_message_to_db(message_info, ch_or_dm_id, token_decoded['auth_user_id'], \
        to_channel)

    return message_id

# message_remove_v1 is used for message/remove/v1
def message_remove_v1(token: AnyStr, message_id: int) -> dict:
    '''
    Given a message_id for a message, this message is removed from the channel/DM.
    
    Arguments:
        token <bytes> - unique user token
        message_id <int> - unique channel id

    Exceptions:
        InputError  - Occurs when message_id does not exist.
        AccessError - Occurs when token does not exist or an unauthorised user
                      is trying to delete the message.

    Return Value:
        None
    '''
    
    msg_idx, msg, msg_in_channel = message_errors(token, message_id)

    if msg_in_channel:
        del channels[msg['dest_id']]['messages'][msg_idx]
    else:
        del dms[msg['dest_id']]['messages'][msg_idx]

    return {}

# message_edit_v1 is used for message/edit/v1
def message_edit_v1(token: AnyStr, message_id: int, edited_message: str) -> dict:
    '''
    Given a message, update its text with new text. If the new message is an 
    empty string, the message is deleted.
    
    Arguments:
        token <bytes> - unique user token
        message_id <int> - unique channel id
        edited_message <string> - message after edited changes 

    Exceptions:
        InputError  - Occurs when message length is not between 1 and 1000 characters.

    Return Value:
        None
    '''
    token_decoded = helper.check_token(token)

    msg_idx, msg, msg_in_channel = message_errors(token, message_id)

    if len(edited_message) > 1000:
        raise InputError('Invalid Message: Message must be within 1000 characters')
    elif len(edited_message) == 0: # Delete message at message index in list
        if msg_in_channel:
            del channels[msg['dest_id']]['messages'][msg_idx]
        else:
            del dms[msg['dest_id']]['messages'][msg_idx]
    else: # Edit message
        if msg_in_channel:
            channels[msg['dest_id']]['messages'][msg_idx]['message'] = edited_message
            check_message_tags(edited_message, token_decoded['auth_user_id'], msg['dest_id'], -1)
        else:
            dms[msg['dest_id']]['messages'][msg_idx]['message'] = edited_message
            check_message_tags(edited_message, token_decoded['auth_user_id'], -1, msg['dest_id'])

    return {}

# message_share_v1 is used for message/share/v1
def message_share_v1(token: AnyStr, og_message_id: int, optional_message: str, channel_id: int, dm_id: int) -> dict:
    '''
    Given a message, update its text with new text. If the new message is an 
    empty string, the message is deleted.
    
    Arguments:
        token <bytes> - unique user token
        og_message_id <int> - unique message id of original message being shared
        optional_message <string> - optional message sent with shared message
        channel_id <int> - unique channel_id that the message is being shared to;
                            if -1, message is being shared to dm
        dm_id <int> - unique dm_id that the message is being share to

    Exceptions:
        InputError  - Occurs when message length is not between 1 and 1000 characters.

    Return Value:
        shared_message_id - message_id of shared message
    '''

    token_decoded = helper.check_token(token)

    msg_idx, msg, msg_in_channel = message_errors(token, og_message_id)
    new_message = ''
    # Extract message from og_message_id and assign to new_message string
    if msg_in_channel:
        new_message = channels[msg['dest_id']]['messages'][msg_idx]['message']
    else:
        new_message = dms[msg['dest_id']]['messages'][msg_idx]['message']

    # Identify if there is an additional optional message
    if optional_message != '':
        new_message = new_message + "\n\t--- " + optional_message

    if (channel_id != -1): # message is being shared to channel_id
        # Check user is in the channel they are sharing the message to
        helper.user_in_channel_check(token_decoded['auth_user_id'], channel_id)
        # Send the message
        shared_message_id = message_send_v1(token, channel_id, new_message, True)

    if (dm_id != -1): # message is being shared to dm_id
        # Check user is in the DM they are sharing the message to
        helper.user_in_dm_check(token_decoded['auth_user_id'], dm_id)
        # Send the message
        shared_message_id = message_send_v1(token, dm_id, new_message, False)

    return shared_message_id

def message_send_later_v1(token: AnyStr, ch_or_dm_id: int, message: str, to_channel: bool, time_sent: int) -> dict:
    '''
    Sends a message from an authorised user to the channel/dm specified.

    Arguments:
        token <bytes> - unique user token
        ch_or_dm_id <int> - unique channel/dm id
        message <string> - message that is to be sent to the channel/dm
        to_channel <bool> - boolean that is True if message destination is a channel
                            and False for dms
        time_sent <int> - unix timestamp

    Exceptions:
        InputError  - Occurs when channel/dm does not exist or message length
                      is not between 1 and 1000 characters or if time_sent is a timestamp
                      from the past.
        AccessError - Occurs when token does not exist or user is not in channel/dm
                      list.

    Return Value:
        Returns the unique message_id for the message
    '''

    token_decoded = helper.check_token(token)

    helper.token_check(token)
    helper.channel_check(ch_or_dm_id) if (to_channel) else helper.dm_check(ch_or_dm_id)
    helper.user_in_channel_check(token_decoded['auth_user_id'], ch_or_dm_id) if (to_channel) else \
        helper.user_in_dm_check(token_decoded['auth_user_id'], ch_or_dm_id)

    if len(message) > 1000 or len(message) == 0:
        raise InputError(description='Invalid Message: Message must be within 1000 characters')

    if time_sent < int(datetime.now().replace(tzinfo=timezone.utc).timestamp()):
        raise InputError(description='Invalid Time: Time entered is in the past')

    wait_time = time_sent - datetime.now().replace(tzinfo=timezone.utc).timestamp() 

    message_id = helper.uniqid()
    
    message_info = {
        'message_id': message_id,
        'dest_id': ch_or_dm_id,
        'u_id': token_decoded['auth_user_id'],
        'message': message,
        'time_created': time_sent,
    }

    threading.Timer(wait_time, add_message_to_db, args=[message_info, ch_or_dm_id, #
                    token_decoded['auth_user_id'], to_channel]).start()

    return message_id

def message_react_v1(token: AnyStr, message_id: int, react_id: int) -> dict:
    '''
    Given a message within a channel or DM the authorised user is part 
    of, add a "react" to that particular message
    
    Arguments:
        token <bytes> - unique user token
        message_id <int> - unique message id
        react_id <int> - reaction of the authorised user

    Exceptions:
        InputError:
            message_id is not a valid message within a channel or DM that the authorised user has joined
            react_id is not a valid React ID. The only valid react ID the frontend has is 1
            Message with ID message_id already contains an active React with ID react_id from the authorised user
            
        AccessError:
            Token is invalid
            The authorised user is not a member of the channel or DM that the message is within

    Return Value:
        An empty dictionary
    '''
    # Check is token valid
    helper.token_check(token)
    
    #react_id is not a valid React ID
    if not isinstance(react_id, int) or react_id is not REACT:
        raise InputError('react_id is not a valid React ID')
    
    m_in_channel = message_channel_check(message_id)
    m_in_dm = message_dm_check(message_id)
    if m_in_channel is not None or m_in_dm is not None:

        #The authorised user is not a member of the channel or DM that the message is within
        u_id = helper.get_u_id(token)
        if m_in_channel is None:
            m = m_in_dm[1]
            helper.user_in_dm_check(u_id, m_in_dm[2])
        else:
            m = m_in_channel[1]
            helper.user_in_channel_check(u_id, m_in_channel[2])

        for r in m['reacts']:
            if r['react_id'] == react_id:
                #Message with ID message_id already contains an active React with ID react_id from the authorised user
                if r['is_this_user_reacted']:
                    raise InputError("User already reacted")

                #React a message
                r['u_ids'].append(u_id)
                r['is_this_user_reacted'] = True
    # Check is message_id a valid message within a channel or DM that the authorised user has joined
    else:
        raise InputError('Invalid message id')

    return {}

def message_unreact_v1(token: AnyStr, message_id: int, react_id: int) -> dict:
    '''
    Given a message within a channel or DM the authorised user is part of, remove a "react" to that particular message
    
    Arguments:
        token <bytes> - unique user token
        message_id <int> - unique message id
        react_id <int> - reaction of the authorised user

    Exceptions:
        InputError:
            message_id is not a valid message within a channel or DM that the authorised user has joined
            react_id is not a valid React ID. The only valid react ID the frontend has is 1
            Message with ID message_id does not contain an active React with ID react_id from the authorised user
            
        AccessError:
            Token is invalid
            The authorised user is not a member of the channel or DM that the message is within

    Return Value:
        An empty dictionary
    '''
    # Check is token valid
    helper.token_check(token)
    
    #react_id is not a valid React ID
    if not isinstance(react_id, int) or react_id is not REACT:
        raise InputError(description='react_id is not a valid React ID')
    
    #Message with ID message_id already contains an active React with ID react_id from the authorised user
    m_in_channel = message_channel_check(message_id)
    m_in_dm = message_dm_check(message_id)
    if m_in_channel is not None or m_in_dm is not None:

        #The authorised user is not a member of the channel or DM that the message is within
        u_id = helper.get_u_id(token)
        if m_in_channel is None:
            m = m_in_dm[1]
            helper.user_in_dm_check(u_id, m_in_dm[2])
        else:
            m = m_in_channel[1]
            helper.user_in_channel_check(u_id, m_in_channel[2])

        for r in m['reacts']:
            if r['react_id'] == react_id:
                if not r['is_this_user_reacted']:
                    raise InputError(description="User did not reacted")

                #Unreact a message
                r['u_ids'].remove(u_id)
                r['is_this_user_reacted'] = False

    # Message with ID message_id does not contain an active React with ID react_id from the authorised user
    else:
        raise InputError(description='Invalid Message: Message ID does not exist')
    
    return {}

def message_pin_unpin_v1(token: AnyStr, message_id: int, pin: bool) -> dict:
    '''
    Given a message within a channel or DM, marks it as a pinned/unpinned message.

    Arguments:
        token <bytes> - unique user token
        message_id <int> - unique message id
        pin <bool> - True if message_pin is called and false if message_unpin is called

    Exceptions:
        InputError  - Occurs when message does not exist or message is already pinned/unpinned.
        AccessError - Occurs when user is not a member or an owner of the channel/dm
                      that the message is in.

    Return Value:
        Returns an empty dictionary
    '''

    token_decoded = helper.check_token(token)
    helper.token_check(token)

    # Destructure message_values
    msg_in_channel = check_message_exists(message_id).get('in_channel')
    msg_idx, _, ch_or_dm_id = check_message_exists(message_id).get('message_values')

    # Check authorisation: user must be a member and an owner of the channel/dm (2 separate errors)
    if (msg_in_channel):
        user_info = helper.user_info(token_decoded['auth_user_id'])
        if user_info not in channels[ch_or_dm_id]['all_members']:
            raise AccessError(description='Unauthorised User: User not a channel member')
        elif user_info not in channels[ch_or_dm_id]['owner_members']:
            raise AccessError(description='Unauthorised User: User not a channel owner')
        
        if pin:
            # Raise error is message is already pinned
            if channels[ch_or_dm_id]['messages'][msg_idx]['is_pinned']:
                raise InputError(description='Error: Message is already pinned')
            else:
                channels[ch_or_dm_id]['messages'][msg_idx]['is_pinned'] = True
        else:
            # Raise error is message is already unpinned
            if not channels[ch_or_dm_id]['messages'][msg_idx]['is_pinned']:
                raise InputError(description='Error: Message is already unpinned')
            else:
                channels[ch_or_dm_id]['messages'][msg_idx]['is_pinned'] = False
    else: 
        if token_decoded['auth_user_id'] != dms[ch_or_dm_id]['owner']:
            raise AccessError(description='Unauthorised User: User not a dm owner')
        
        if pin:
            # Raise error is message is already pinned
            if dms[ch_or_dm_id]['messages'][msg_idx]['is_pinned']:
                raise InputError(description='Error: Message is already pinned')
            else:
                dms[ch_or_dm_id]['messages'][msg_idx]['is_pinned'] = True
        else:
            # Raise error is message is already unpinned
            if not dms[ch_or_dm_id]['messages'][msg_idx]['is_pinned']:
                raise InputError(description='Error: Message is already unpinned')
            else:
                dms[ch_or_dm_id]['messages'][msg_idx]['is_pinned'] = False

    return {}
    
############################## UTILITY FUNCTIONS ##############################

def message_errors(token: AnyStr, message_id: int) -> tuple:
    '''
    Raises exceptions for message_edit and message_remove features.

    Exceptions:
        InputError  - Occurs when message_id does not exist.
        AccessError - Occurs when token does not exist or an unauthorised user
                      is making changes.

    Return Value:
        Tuple containing Message index and Message string
    '''

    token_decoded = helper.check_token(token)

    # Destructure message_values
    msg_in_channel = check_message_exists(message_id).get('in_channel')
    msg_idx, msg, ch_or_dm_id = check_message_exists(message_id).get('message_values')
    
    helper.token_check(token)
    # Check authorisation: user is either the global owner of Dreams, message owner, or an owner of the channel/dm 
    if not users[token_decoded['auth_user_id']]['permission_id'] == 1 and token_decoded['auth_user_id'] != msg['u_id']:
        if (msg_in_channel and helper.user_info(token_decoded['auth_user_id']) not in channels[ch_or_dm_id]['owner_members']) \
            or (not msg_in_channel and token_decoded['auth_user_id'] != dms[ch_or_dm_id]['owner']):
            raise AccessError(description='Unauthorised User: Cannot edit message')

    return (msg_idx, msg, msg_in_channel)

def check_message_exists(message_id: int) -> dict:
    # Check if message is in a channel
    message_values = message_channel_check(message_id)
    msg_in_channel = True
    # If message_values is None, check if message is in a DM
    if (message_values == None):
        msg_in_channel = False
        message_values = message_dm_check(message_id)
    # If message_values is still None, message was not found --> return Input Error
    if (message_values == None):
        raise InputError(description='Invalid Message: Message ID does not exist')
    
    return {
        'in_channel': msg_in_channel, 
        'message_values': message_values
    }

def message_channel_check(message_id: int) -> Optional[tuple]:
    '''
    Checks if message_id exists in channel database
    '''
    for channel_id in channels:
        for idx, msg in enumerate(channels[channel_id]['messages']):
            if msg['message_id'] == message_id:
                return (idx, msg, channel_id)
    return None

def message_dm_check(message_id: int) -> Optional[tuple]:
    '''
    Checks if message_id exists in dm database
    '''
    for dm_id in dms:
        for idx, msg in enumerate(dms[dm_id]['messages']):
            if msg['message_id'] == message_id:
                return (idx, msg, dm_id)
    return None

def check_message_tags(message: str, auth_user_id: int, channel_id: int, dm_id: int) -> None:
    '''
    Finds tags in a message that start with '@' and if they exist,
    sends a notification to the user's database saying they have been
    tagged.
    '''
    deconstructed_message = message.split()
    for word in deconstructed_message:
        if word.startswith('@'):
            extract_handle = word[1:]
            user = helper.check_handle(extract_handle)
            if user:
                notify(auth_user_id, user, channel_id, dm_id, message, True)

def add_message_to_db(message_info: dict, ch_or_dm_id: int, auth_user_id: int, to_channel: bool) -> None:
    channels[ch_or_dm_id]['messages'].insert(0, message_info) if (to_channel) else \
        dms[ch_or_dm_id]['messages'].insert(0, message_info)

    check_message_tags(message_info['message'], auth_user_id, ch_or_dm_id, -1) if (to_channel) else \
    check_message_tags(message_info['message'], auth_user_id, -1, ch_or_dm_id)