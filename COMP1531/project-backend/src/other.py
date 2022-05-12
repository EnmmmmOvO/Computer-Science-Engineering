from src.data import users, channels, dms
import src.helper as helper

def clear_v1():
    '''
    Function will clear the dictionary/internal data of given feature
        
    '''
    # Clear all users
    users.clear()
    # Clear all channels
    channels.clear()
    # Clear all dms
    dms.clear()

    return {}

def notify(auth_user_id, invitee_u_id, channel_id, dm_id, message, tagged):
    '''
    Add a notification to a user's list of notifications if the user has
    been tagged or added to a new channel/dm.
    
    Arguments:
        auth_user_id <int> - user id of person sending the message or inviting
                             user to channel/dm
        invitee_u_id <int> - user id of person tagged in message or invited to
                             channel/dm
        channel_id <int> - unique channel_id that the message is being shared to;
                            if -1, if refering to dm
        dm_id <int> - unique dm_id that the message is being share to;
                        if -1, if refering to channel
        message <str> - message being sent; empty string if notification is for
                        channel/dm invitation

    '''
    # Crop message to 20 characters
    if (len(message) > 20):
        message = message[:20]
    # Find name of channel/dm
    ch_or_dm_name = channels[channel_id]['name'] if (channel_id != -1) else dms[dm_id]['name']

    if tagged:
        message = f"{users[auth_user_id]['handle_str']} tagged you in {ch_or_dm_name}: {message}"
    else:
        message = f"{users[auth_user_id]['handle_str']} added you to {ch_or_dm_name}"
    
    notification_info = {
        'channel_id' : channel_id,
        'dm_id' : dm_id,
        'notification_message' : message
    }

    users[invitee_u_id]['notifications'].insert(0, notification_info)

def get_notifications_v1(token):
    '''
    Return the user's most recent 20 notifications
    
    Exceptions:
        AccessError - occurs when token does not exist
    Arguments:
        token <bytes> - unique user token
    '''

    token_decoded = helper.check_token(token)
    helper.token_check(token)

    # Grab the first 20 notifications
    recent_notifications = users[token_decoded['auth_user_id']]['notifications'][:20]

    return recent_notifications
