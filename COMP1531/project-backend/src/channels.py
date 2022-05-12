import uuid
from src.error import InputError, AccessError
from src.data import users, channels
import src.helper as helper

def channels_list_v1(token):

    '''
    Provide a list of all channels (and their associated details) that the authorised
    user is part of

    Arguments: token <bytes> - unique user token

    Return: channel [] - A dictionary containing a list of channels that the user is in
    Errors: AccessError if auth_user_id is invalid 
    '''

    token_decoded = helper.check_token(token)

    #error for auth_user_id
    helper.token_check(token)

    #Intialise an empty dictionary that has a 'channels' list
    user_channels = []

    #Get u_id, name_first, name_last to see if they are a member of a channel
    user_check = helper.user_info(token_decoded['auth_user_id'])

    #Search through each channel in data
    #If the user is a member of a channel:  append it to the channel_list
    for channel_id in channels:
        if user_check in channels[channel_id]['all_members']:
            channel_tmp = helper.channel_info(channel_id)
            user_channels.append(channel_tmp)

    return user_channels

def channels_listall_v1(token):
    
    '''
    Provide a list of all channels (and their associated details)
    Arguments: token <bytes> - unique user token

    Return: channel [] - A dictionary containing a list of all channels
    
    Errors: AccessError if auth_user_id is invalid 
    '''

    #error for auth_user_id
    helper.token_check(token)

    list_all_channels = []
    
    # Create a list of all channel (extract the list from data.channel)
    for channel_id in channels:
        channel_tmp = helper.channel_info(channel_id)
        list_all_channels.append(channel_tmp)

    return list_all_channels

def channels_create_v1(token, name, is_public):
    '''
    Function creates a new channel with given name by user id that can
    be either public or private 
    
    Arguments:
        token <bytes> - unique user token
        name <string> - name of channel
        is_public <boolean> - identifies whether public or private
    
    Exceptions:
        InputError - Occurs when name length exceeds 20 characters
        AccessError - Occurs when user creating channel is not registered
        
    Return Value:
        Returns the channel_id number after it has been created in order
    
    '''

    token_decoded = helper.check_token(token)

    # Check if token is valid
    helper.token_check(token)

    # InputError for name that exceeds 20 characters
    if len(name)>20:
        raise InputError('Channel name is too long')
    
    creator_info = helper.user_info(token_decoded['auth_user_id'])

    # Create channel
    new_channel = {
        'name': name,
        'public' : is_public,
        'owner_members': [creator_info],
        'all_members': [creator_info],
        'messages': [],
        'is_active': False,
        'buffer': []
    }
    
    channel_id = helper.uniqid()
    channels[channel_id] = new_channel

    return channel_id

   
