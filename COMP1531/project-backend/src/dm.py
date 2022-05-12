import uuid
from src.data import users, dms
from src.error import InputError, AccessError
from src.auth import auth_register_v1, generate_token
from src.other import clear_v1, notify
import src.helper as helper  

def dm_details_v1(token, dm_id):
    '''
    Users that are part of this direct message can view basic information
    about the DM

    Arguments:
        token (string): unique user token
        dm_id (integer): id of the interested DM

    Exceptions:
        AccessError:
            - auth_user_id is not a member of thsi DM with dm_id
        InputError: 
            - auth_user_id does not refer to a valid user
            - dm_id does not refer to a valid DM

    Return Value:
        dict: {name, members}
    '''

    token_decoded = helper.check_token(token)
    helper.token_check(token)

    auth_user_id = token_decoded['auth_user_id']
    helper.user_check(auth_user_id)

    helper.dm_check(dm_id)
    helper.user_in_dm_check(auth_user_id, dm_id)

    return {'name': dms[dm_id]['name'], 'members': dms[dm_id]['members']}


def dm_list_v1(token):
    '''
    Returns the list of DMs that the user is a member of

    Arguments:
        token (string): unique user token

    Exceptions:
        InputError: 
            - auth_user_id does not refer to a valid user

    Return Value:
        list: dms
    '''

    token_decoded = helper.check_token(token)
    helper.token_check(token)

    auth_user_id = token_decoded['auth_user_id']
    helper.user_check(auth_user_id)

    related_dms = list(filter(lambda dm: auth_user_id in dm['members'], dms.values()))
    owners = list(filter(lambda dm: auth_user_id == dm['owner'], dms.values()))
    related_dms = related_dms + owners
    related_dms = list(map(lambda dm: {'dm_id': dm['dm_id'], 'name': dm['name']}, related_dms))
    return related_dms
 

def dm_create_v1(token, u_ids):
    '''
    Create a DM to users with u_ids

    Arguments:
        token (string): unique user token
        u_ids: user(s) that this DM is directed to

    Exceptions:
        InputError: 
            - auth_user_id does not refer to a valid user
            - any of u_id does not refer to a valid user

    Return Value:
        dict: {dm_id, dm_name}
    '''

    token_decoded = helper.check_token(token)
    helper.token_check(token)

    auth_user_id = token_decoded['auth_user_id']
    helper.user_check(auth_user_id)
    for u_id in u_ids:
        helper.user_check(u_id)
    
    dm_id = helper.uniqid()
    u_handles = [users[u_id]['handle_str'] for u_id in u_ids]
    u_handles.append(users[auth_user_id]['handle_str'])
    u_handles = sorted(u_handles)
    name = ','.join(u_handles)
    dms[dm_id] = {
        'dm_id': dm_id,
        'name': name,
        'owner': auth_user_id,
        'members': u_ids,
        'messages': []
    }
    
    for u_id in u_ids:
        notify(token_decoded['auth_user_id'], u_id, -1, dm_id, "", False)

    return {
        'dm_id': dm_id, 
        'dm_name': name
    }

def dm_remove_v1(token, dm_id):
    '''
    Remove an existing DM. This can only be done by the original creator
    of the DM.

    Arguments:
        token (string): unique user token
        dm_id (integer): id of the interested DM

    Exceptions:
        AccessError:
            - the user with auth_user_id is not the original DM creator
        InputError: 
            - auth_user_id does not refer to a valid user
            - dm_id does not refer to a valid DM

    Return Value:
        dict: {}
    '''

    token_decoded = helper.check_token(token)
    auth_user_id = token_decoded['auth_user_id']

    helper.token_check(token)
    helper.user_check(auth_user_id)
    helper.dm_check(dm_id)
    helper.user_own_dm_check(auth_user_id, dm_id)

    del dms[dm_id]
    return {}

def dm_invite_v1(token, dm_id, u_id):
    '''
    Inviting a user to an existing dm. 

    Arguments:
        token (string): unique user token
        dm_id (integer): unique DM id that authorised user is part of 
        u_id (int): unique id of invited user

    Exceptions:
        AccessError:
            - the authorised user is not already a member of the DM
        InputError: 
            - dm_id does not refer to an existing dm.
            - u_id does not refer to a valid user.

    Return Value:
        dict: {}
    '''   

    
    # Input check
    token_decoded = helper.check_token(token)
    helper.token_check(token)

    auth_user_id = token_decoded['auth_user_id']
    helper.user_check(auth_user_id)
    
    helper.dm_check(dm_id)
    helper.user_in_dm_check(auth_user_id, dm_id)
    
    helper.user_check(u_id)

    # Add user with u_id
    if u_id not in dms[dm_id]['members']:
        dms[dm_id]['members'].append(u_id)
        notify(token_decoded['auth_user_id'], u_id, -1, dm_id, "", False)

    return {}



def dm_leave_v1(token, dm_id):
    '''
    Given a DM ID, the user is removed as a member of this DM.  

    Arguments:
        token (string): unique user token
        dm_id (integer): unique DM id that authorised user is part of 

    Exceptions:
        AccessError:
            - Authorised user is not a member of DM with dm_id
        InputError: 
            - dm_id is not a valid DM

    Return Value:
        dict: {}
    ''' 
    token_decoded = helper.check_token(token)
    helper.token_check(token)
    
    auth_user_id = token_decoded['auth_user_id']
    helper.user_check(auth_user_id)
    helper.dm_check(dm_id)
    helper.user_in_dm_check(auth_user_id, dm_id)
    
    if auth_user_id == dms[dm_id]['owner']:
        dms[dm_id]['owner'] = None
    else:
        idx = dms[dm_id]['members'].index(auth_user_id)
        del dms[dm_id]['members'][idx]

    return {}

def dm_messages_v1(token, dm_id, start):
    '''
    Given a DM with ID dm_id that the authorised user is part of,
    return up to 50 messages between index "start" and "start + 50". 

    Arguments:
        token (string): unique user token
        dm_id (integer): unique DM id that authorised user is part of 
        start (integer) index for message number

    Exceptions:
        AccessError:
            - Authorised user is not a member of DM with dm_id
            - start is greater than the total number of messages in the channel
        InputError: 
            - dm_id is not a valid DM

    Return Value:
        Returns a dictionary consisting of a list of 'messages' (less than 50)
	    as well as 'start' and 'end' values. Returns start + 50 in end
        value if not all messages have loaded. Returns -1 in end if oldest messages
	    have been loaded.

    ''' 
    token_decoded = helper.check_token(token)
    helper.token_check(token)
    
    helper.dm_check(dm_id)
    helper.user_in_dm_check(token_decoded['auth_user_id'], dm_id)

    message_list = [message for message in dms[dm_id]['messages']]
    if start < 0 or start > len(message_list):
        raise InputError('Invalid Index Value: Message index does not exist')

    # Assuming 0 < start < len(message_list)
    if len(message_list[start:]) < 50:
        end = -1
    else:
        end = start + 50

    return {
        'messages': message_list[start:] if end == -1 else message_list[start:end],
        'start': start,
        'end': end
    }