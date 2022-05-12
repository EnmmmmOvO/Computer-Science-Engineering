import re
import jwt
import json
import uuid
import hashlib

from src.error import InputError
from src.data import users
import src.helper as helper

#secret for token
SECRET = 'This is a very safe secret'

def auth_register_v1(email, password, name_first, name_last):
    '''
    Given a user's first and last name, email address, and password, 
    create a new account for them
    
    Arguments: 
        email <str> - email of users
        password <str> - password of users
        name_first <str> - first name of users
        name_last <str> - last name of users
    
    Exceptions:
        InputError:
            Email entered is not a valid email using the method provided here (unless you feel you have a better method).
            Email address is already being used by another user
            Password entered is less than 6 characters long
            name_first is not between 1 and 50 characters inclusively in length
            name_last is not between 1 and 50 characters inclusively in length
    
    Return value:
        return a new 'token' for that session and user id
    '''

    #Email entered is not a valid email
    if re.search('^[a-zA-Z0-9]+[\\._]?[a-zA-Z0-9]+[@]\\w+[.]\\w{2,3}$', email) == None:
        raise InputError('Invalid email.')
        
    #Email address is already being used by another
    email_exists = False 
    if len(users) > 0:
        for user in users: 
            if users[user]['email'] == email:
                email_exists = True
    if email_exists is True:
        raise InputError('Email address is already being used by another.')

    #Password entered is less than 6 characters long
    if len(password) < 6:
        raise InputError('Password is too short.')

    #name_first is not between 1 and 50 characters inclusively in length
    if not (1 <= len(name_first) <= 50):
        raise InputError('First name is too short or too long.')
        
    #name_last is not between 1 and 50 characters inclusively in length
    if not (1 <= len(name_last) <= 50):        
        raise InputError('Last name is too short or too long.')

    #generate a handle
    handle = make_handle(name_first, name_last)

    #return user id
    u_id = len(users) + 1
    
    users[u_id] = {
        'session_id': [],
        'permission_id': 2,
        'email' : email,
        'password' : hashlib.sha256(password.encode()).hexdigest(),
        'name_first' : name_first,
        'name_last' : name_last,
        'handle_str': handle,
        'notifications' : []
    }

    if u_id == 1:
        users[u_id]['permission_id'] = 1         

    #return a new token
    s_id = new_session_id()
    users[u_id]['session_id'].append(s_id)
    token = generate_token(s_id)
    return {'token': token, 'auth_user_id': u_id}

def auth_login_v1(email, password):
    '''
    Given a registered users' email and password and returns a new 
    `token` for that session
    
    Arguments:
        email <str> - email of users
        password <str> - password of users
    
    Exceptions:
        InputError:
            Email entered is not a valid email
            Email entered does not belong to a user
            Password is not correct
            
    Return value:
        return a new 'token' for that session and user id
    '''

    #Email entered is not a valid email
    if re.search('^[a-zA-Z0-9]+[\\._]?[a-zA-Z0-9]+[@]\\w+[.]\\w{2,3}$', email) == None:
        raise InputError('Invalid email.')

    #Email entered does not belong to a user 
    email_exists = False 
    for user in users: 
        if users[user]['email'] == email:
            u_id = user
            email_exists = True
    if email_exists is False:
        raise InputError('Email does not belong to a user.')

    #Password is not correct
    if hashlib.sha256(password.encode()).hexdigest() != users[u_id]['password']:
        raise InputError('Incorrect password. Please try again.')
        
    #Return auth_user_id and a new token
    s_id = new_session_id()
    users[u_id]['session_id'].append(s_id)
    token = generate_token(s_id)
    return {'token': token, 'auth_user_id': u_id}

def auth_logout_v1(token):
    '''
    Given an active token, invalidates the token to log the user out. 
    If a valid token is given, and the user is successfully logged 
    out, it returns true, otherwise false.
    
    Arguments:
        email <str> - email of users
        password <str> - password of users
    
    Exceptions: N/A
            
    Return value:
        if users are logout successfully, return true. Otherwise, 
        return false.
    '''

    #Token passed is valid or not
    helper.token_check(token)

    #Given an active token, invalidates the token to log the user out.
    decode = jwt.decode(token, SECRET, algorithms = ['HS256'])
    s_id = decode['session_id']
    global users
    for user in users:
        for status in users[user]['session_id']:
            if status == s_id:
                users[user]['session_id'].remove(s_id)
                return {'is_success': True}
    return {'is_success': False}

### Helper Functions ###

def generate_token(s_id):
#generate a token
    return jwt.encode({'session_id': s_id}, SECRET, algorithm = 'HS256')

def new_session_id():
#get a new session_id
    return str(uuid.uuid1())

def make_handle(name_first, name_last):
    concat = name_first + name_last
    concat = concat.lower()
    if len(concat) > 20:
        concat = concat[:20]
    copy_concat = concat
    append_number = 0
    while True:
        for user in users:
            if users[user]['handle_str'] == copy_concat:
                copy_concat = concat + str(append_number)
                append_number += 1
                continue
        return copy_concat
