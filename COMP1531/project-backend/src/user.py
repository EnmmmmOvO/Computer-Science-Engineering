import re
import uuid
import src.helper as helper 
from typing import AnyStr
from src.data import users
from src.auth import generate_token, new_session_id
from src.error import InputError

def convert_to_user_profile(auth_user_id: int) -> dict:
    '''
    Generates profile for user 
        
    Return Value:
        'user' - dictionary containing user profile 
    
    '''
    return {
        'u_id': auth_user_id,
        'email': users[auth_user_id]['email'],
        'name_first': users[auth_user_id]['name_first'],
        'name_last': users[auth_user_id]['name_last'],
        'handle_str': users[auth_user_id]['handle_str'],
    }
    
def users_all_v1(token: AnyStr) -> dict: 
    '''
    Reads a list of all users and associated profiles including u_id, first name,
    last name, email and hadle
    
    Arguments: 
        token <bytes> - unique user token

    Return Value:
        Returns a list of all users 
    
    '''
    
    helper.token_check(token)
    
    all_users = []
    for user in users:
        all_users.append(convert_to_user_profile(user))
    return {
        'users': all_users
    }
    
def user_profile_v2(token: AnyStr, u_id: int) -> dict:
    '''
    For a valid user, this will return a user profile including user id, email, first name, last name and handle.
    
    Arguments: 
        token <bytes> - unique user token 
        u_id <int> - unique user id
        
    Exceptions:
        InputError - invalid user with u_id
    
    Return Value:
        Returns user profile 
    
    '''
    helper.token_check(token)
    helper.user_check(u_id)
    
    return {
        'user' : convert_to_user_profile(u_id)
    }


def user_profile_setname_v2(token: AnyStr, name_first: str, name_last: str) -> dict:
    '''
    Updates the authorised user's first name and last name in profile
    
    Arguments: 
        token <bytes> - unique user token
        name_first <string> - user first name 
        name_last <string> - user last name 
    
    Exceptions:
        InputError - when name_first and name_last is not between 1 and 
                     50 characters 
    Return Value:
        Returns updated user profile
    
    '''
    token_decoded = helper.check_token(token)
    helper.token_check(token)
    
    
    if name_first is None or len(name_first)>50 or len(name_first)<1:
        raise InputError(description='Invalid name_first!')
        
    if name_last is None or len(name_last)>50 or len(name_last)<1:
        raise InputError(description='Invalid name_last!')
        
    users[token_decoded['auth_user_id']]['name_last'] = name_last
    users[token_decoded['auth_user_id']]['name_first'] = name_first
            
    return {}
    
        
def user_profile_setemail_v2(token: AnyStr, email: str) -> dict:
    '''
    Updates the user email address
    
    Arguments: 
        token <bytes> - unique user token
        email <string> - user email
    
    Exceptions:
        InputError - when email entered is invalid
    
    Return Value:
        Returns new user email 
    
    '''
    token_decoded = helper.check_token(token)
    helper.token_check(token)
    
    email_regex = "^[a-zA-Z0-9]+[\\._]?[a-zA-Z0-9]+[@]\\w+[.]\\w{2,3}$"
    
    if len(email) > 254:
        raise InputError(description='Invalid email address!')
    if email is None or not re.search(email_regex, email):
        raise InputError(description='Invalid email address!')
        
    for user in users: 
        if users[user]['email'] == email and user != token_decoded['auth_user_id']:
            raise InputError(description='Email address is already being used by another.')
    
    users[token_decoded['auth_user_id']]['email'] = email
    
    return {}

def user_profile_sethandle_v2(token: AnyStr, handle_str: str) -> dict:
    '''
    Updates authorised user handle 
    
    Arguments: 
        token <bytes> - unique user token
        handle_str <string> - user handle 
    
    Exceptions:
        InputError - when handle_str is not between 3 and 20 characters or is
                     already being used by another user
    
    Return Value:
        returns user with updated handle 
    
    '''
    token_decoded = helper.check_token(token)
    helper.token_check(token)
    
    if handle_str is None or len(handle_str) < 3 or len(handle_str) > 20:
        raise InputError(description='Invalid length of handle_str!')
  
    # Check for existing handle_str
    for user in users: 
        if users[user]['handle_str'] == handle_str and user != token_decoded['auth_user_id']:
            raise InputError(description='Email address is already being used by another user.')        
    
    # Change handle
    users[token_decoded['auth_user_id']]['handle_str'] = handle_str
            
    return {}
