import jwt

from src.channels import channels_list_v1
from src.channel import channel_messages_v1
from src.dm import dm_list_v1, dm_messages_v1
from src.error import InputError
from src.data import users, channels, dms, save_db
import src.helper as helper

#secret for token
SECRET = 'This is a very safe secret'

def search_v2(token, query_str):
    '''
    Given a query string, return a collection of messages in all of 
    the channels/DMs that the user has joined that match the query
    
    Arguments:
        token <bytes> - unique user token
        query_str <str> - a string to search messages

    Exceptions:
        AccessError:
            token passed in is a invalid token
        InputError:
            query_str is above 1000 characters

    Return value:
        List of dictionaries, where each dictionary contains types { message_id, u_id, message, time_created }
    '''
    
    #Token passed is valid or not
    helper.token_check(token)

    #Check is query_str above 1000 characters
    if len(query_str) > 1000:
        raise InputError('query string is too long.')

    #Return a collection of messages in all of the channels/DMs that the user has joined that match the query
    l = []
    target_channels = channels_list_v1(token)
    for c in target_channels:
        c_id = c['channel_id']
        details = channel_messages_v1(token, c_id, 0)
        for idx, _ in enumerate(details['messages']):
            if query_str in details['messages'][idx]['message']:
                l.append(details['messages'][idx]['message'])
    target_dms = dm_list_v1(token)
    for d in target_dms:
        d_id = d['dm_id']
        details = dm_messages_v1(token, d_id, 0)
        for idx, _ in enumerate(details['messages']):
            if query_str in details['messages'][idx]['message']:
                l.append(details['messages'][idx]['message'])
    return l
