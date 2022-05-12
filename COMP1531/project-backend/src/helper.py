import jwt
from time import time
from src.data import users, channels, dms
from src.error import InputError, AccessError

#secret for token
SECRET = 'This is a very safe secret'

def check_token(token):
    try:
        payload = jwt.decode(token, SECRET, algorithms=["HS256"])
        session_id = payload['session_id'] 
        status = True
        for user in users:
            if session_id in users[user]['session_id']:
                return {'status' : status, 'auth_user_id' : user}
        user = None
    except jwt.InvalidSignatureError:
        status = False
    return {'status' : status, 'auth_user_id' : None}

def token_check(token):
    '''
    Checks for valid token
    '''
    token_decoded = check_token(token)
    if token_decoded['status'] is False or token_decoded['auth_user_id'] is None:
        raise AccessError(description='Invalid Token: Token does not exist')

def user_check(auth_user_id):
    '''
    Checks for valid auth_user_id
    '''
    for user in users:
        if int(auth_user_id) == user:
            return True
    raise InputError(description='Invalid User: User does not exist')

def channel_check(channel_id):
    '''
    Checks if channel exists
    '''
    if channel_id not in channels: 
        raise InputError(description='Invalid Channel: Channel does not exist')

def dm_check(dm_id):
    '''
    Checks if dm exists
    '''
    if dm_id not in dms: 
        raise InputError(description='Invalid DM: DM does not exist')

def user_in_channel_check(auth_user_id, channel_id):
    '''
    Checks if user is in channel
    '''
    info = user_info(auth_user_id)
    if info not in channels[channel_id]['all_members']:
        raise AccessError(description='Invalid User: User is not in channel list')

def user_in_dm_check(auth_user_id, dm_id):
    '''
    Checks if user is in dm
    '''
    if auth_user_id != dms[dm_id]['owner'] and auth_user_id not in dms[dm_id]['members']:
        raise AccessError(description='Invalid User: User is not in dm list')

def user_own_dm_check(auth_user_id, dm_id):
    '''
    Checks if user is the creator of dm
    '''
    if auth_user_id != dms[dm_id]['owner']:
        raise AccessError(description='Invalid User: User is not the owner')

def user_info(auth_user_id):
    return {
        'u_id': auth_user_id,
        'email': users[auth_user_id]['email'],
        'name_first': users[auth_user_id]['name_first'],
        'name_last': users[auth_user_id]['name_last'],
        'handle_str': users[auth_user_id]['handle_str'],
    }

def channel_info(channel_id):
    return {
        'channel_id': channel_id,
        'name': channels[channel_id]['name']
    }

def check_handle(handle):
    for user in users:
        if users[user]['handle_str'] == handle:
            return user
    return None

def user_own_channel_check(auth_user_id, channel_id):
    '''
    Checks if user is the owner of channel
    '''
    if user_info(auth_user_id) not in channels[channel_id]['owner_members']:
        raise AccessError(description='Invalid User: User is not the owner')

def uniqid():
    x=time()*10000000
    return int(x)

def get_u_id(token):
    decoded = jwt.decode(token, SECRET, algorithms = ['HS256'])
    decoded = decoded['session_id']
    for user in users:
        for s_id in users[user]['session_id']:
            if decoded == s_id:
                return user
