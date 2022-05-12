import jwt
from src.error import InputError, AccessError
from src.data import users, channels
import src.helper as helper

#Permission id
OWNER = 1
MEMBER = 2
#secret for token
SECRET = 'This is a very safe secret'

def admin_user_remove_v1(token, u_id):
    '''
    Given a User by their user ID, remove the user from the Dreams.
    Dreams owners can remove other **Dreams** owners (including the 
    original first owner). Once users are removed from **Dreams**, 
    the contents of the messages they sent will be replaced by 
    'Removed user'. Their profile must still be retrievable with 
    user/profile/v2, with their name replaced by 'Removed user'.
    
    Arguments: 
        token <bytes> - unique user token
        u_id <int> - unique user id
    
    Exceptions:
        InputError:
            User id does not refer to a valid user.
            User id refers to the only current owner.
        AccessError:
            The user specified by the token is not an owner.
    
    Return value:
        return an empty dictionary.
    '''
    token_decoded = helper.check_token(token)
    #Token passed is valid or not
    helper.token_check(token)

    #u_id does not refer to a valid user
    helper.user_check(u_id)

    #Check is authorised user an owner
    if users[token_decoded['auth_user_id']]['permission_id'] != OWNER:
        raise AccessError('The authorised user is not an owner.')
    
    #The user is currently the only owner
    if u_id == token_decoded['auth_user_id']:
        if is_only_owner():
            raise InputError('The user is currently the only owner.')
    
    #Rename the user by 'removed user'
    users[u_id]['name_first'] = 'Removed'
    users[u_id]['name_last'] = 'user'
    users[u_id]['permission_id'] = 0
    #the contents of the messages they sent will be replaced by 'Removed user'
    for c in channels:
        for m in range(len(channels[c]['messages'])):
            if channels[c]['messages'][m]['u_id'] == u_id:
                channels[c]['messages'][m]['message'] = 'Removed user'

    return {}

def admin_userpermission_change_v1(token, u_id, permission_id):
    '''
    Given a User by their user ID, set their permissions to new
    permissions described by permission_id.
    
    Arguments: 
        token <bytes> - unique user token
        u_id <int> - unique user id
        permission_id <int> - number indicating permission status
    
    Exceptions:
        InputError:
            User id does not refer to a valid user.
            Permission id does not refer to a valid permission number.
        AccessError:
            The user specified by the token is not an owner.
    
    Return value:
        return an empty dictionary.
    '''
    token_decoded = helper.check_token(token)

    #Token passed is valid or not
    helper.token_check(token)

    #u_id does not refer to a valid user
    helper.user_check(u_id)

    #Check is authorised user an owner
    if users[token_decoded['auth_user_id']]['permission_id'] != OWNER:
        raise AccessError('The authorised user is not an owner.')
    
    #Check is permission id valid
    if permission_id != OWNER and permission_id != MEMBER:
        raise InputError('permission_id does not refer to a value permission.')

    #Change permission id
    users[u_id]['permission_id'] = permission_id
    
    return {}

### Helper Functions

def is_only_owner():
    owner_num = 0
    for user in users:
        if users[user]['permission_id'] == OWNER:
            owner_num += 1
    if owner_num == 1:
        return True
    return False
