import sys
sys.path.append('.')
import src.data as db
import threading
from time import sleep
from json import dumps
from datetime import datetime, timezone
from flask import Flask, request
from flask_cors import CORS
from src.error import InputError
from src.auth import auth_login_v1, auth_register_v1, auth_logout_v1
from src.admin import admin_user_remove_v1, admin_userpermission_change_v1
from src.message import message_send_v1, message_edit_v1, \
    message_remove_v1, message_share_v1, message_send_later_v1, \
    message_react_v1, message_unreact_v1, message_pin_unpin_v1
from src.channel import channel_invite_v1, channel_details_v1, \
    channel_addowner_v1, channel_removeowner_v1, channel_leave_v1, \
    channel_join_v1, channel_messages_v1
from src.channels import channels_create_v1, channels_list_v1, \
    channels_listall_v1
from src.dm import dm_create_v1, dm_details_v1, dm_list_v1, \
    dm_remove_v1, dm_leave_v1, dm_messages_v1, dm_invite_v1
from src.user import user_profile_v2, user_profile_setname_v2, \
    user_profile_setemail_v2, user_profile_sethandle_v2, users_all_v1
from src.standup import standup_active_v1, standup_send_v1, standup_start_v1
from src.search import search_v2
from src.other import clear_v1, get_notifications_v1
from src import config

def defaultHandler(err):
    response = err.get_response()
    print('response', err, err.get_response())
    response.data = dumps({
        "code": err.code,
        "name": "System Error",
        "message": err.get_description(),
    })
    response.content_type = 'application/json'
    return response

APP = Flask(__name__)
CORS(APP)

APP.config['TRAP_HTTP_EXCEPTIONS'] = True
APP.register_error_handler(Exception, defaultHandler)

###############################################################
#                     ECHO FLASK ROUTE                        #
###############################################################

@APP.route("/echo", methods=['GET'])
def echo():
    ''' 
    Flask wrapper for sample echo function takes in a value and
    returns it in a dictionary.
    '''
    incoming = request.args.get('data')
    if incoming == 'echo':
   	    raise InputError(description='Cannot echo "echo"')
    return dumps({
        'data': incoming
    })

###############################################################
#                    AUTH FLASK ROUTES                        #
###############################################################

@APP.route('/auth/login/v2', methods=['POST'])
def auth_login():
    ''' 
    Flask wrapper for auth_login that takes an email and password,
    and logs the user into Dreams. Returns a dictionary with
    the user token and auth_user_id.
    '''
    incoming = request.get_json()
    return saveAndReturn(auth_login_v1(incoming['email'], \
                            incoming['password']))

@APP.route('/auth/register/v2', methods=['POST'])
def auth_register():
    ''' 
    Flask wrapper for auth_register that takes an email, password
    and the first and last names of a new user, registering the info
    into Dreams and logining the user in. Returns a dictionary with
    the user token and auth_user_id.
    '''
    incoming = request.get_json()
    return saveAndReturn(auth_register_v1(incoming['email'], \
                    incoming['password'], incoming['name_first'], \
                    incoming['name_last']))

@APP.route('/auth/logout/v1', methods=['POST'])
def auth_logout():
    ''' 
    Flask wrapper for auth_logout that takes a token and logs
    the user out of Dreams (invalidating the current token).
    Returns a dictionary with the logout status (true if
    logout was successful and false otherwise)
    '''
    incoming = request.get_json()
    return saveAndReturn(auth_logout_v1(incoming['token']))

###############################################################
#                    CHANNEL(/S) FLASK ROUTES                 #
###############################################################

@APP.route("/channel/invite/v2", methods=["POST"])
def channel_invite():
    '''
    Flask wrapper for channel_invite that takes a token, a
    channel_id and the user id of the user to invite to the 
    given channel. 
    '''
    incoming = request.get_json()
    return saveAndReturn(channel_invite_v1(incoming['token'], \
                    incoming['channel_id'], incoming['u_id']))

@APP.route("/channel/details/v2", methods=["GET"])
def channel_details():
    ''' 
    Flask wrapper for channel_details that takes a token and a 
    channel_id, returning the details of the specified channel 
    (if the user is a member). 
    '''
    return dumps(channel_details_v1(request.args.get('token'), \
                int(request.args.get('channel_id'))))

@APP.route("/channel/messages/v2", methods=["GET"])
def channel_messages():
    ''' 
    Flask wrapper for channel_messages that takes a token, a 
    channel_id and a start value, returning a list of up to 50 
    messages between index "start" and "start + 50". Also returns 
    the start valueand end value (-1 if the oldest messages have 
    been returned). 
    '''
    return dumps(channel_messages_v1(request.args.get('token'), \
                                        int(request.args.get('channel_id')), \
                                        int(request.args.get('start'))))

@APP.route("/channel/join/v2", methods=["POST"])
def channel_join():
    ''' 
    Flask wrapper for channel_join that takes a token and 
    a channel_id, adding the user to the specified channel.
    '''
    incoming = request.get_json()
    channel_join_v1(incoming['token'], incoming['channel_id'])
    return saveAndReturn({})

@APP.route("/channel/addowner/v1", methods=["POST"])
def channel_add_owner():
    ''' 
    Flask wrapper for channel_addowner that takes a token 
    (of a Dreams/channel owner), channel_id and a user id, and 
    removes owner status from the specified user.
    '''
    incoming = request.get_json()
    return saveAndReturn(channel_addowner_v1(incoming['token'], \
        incoming['channel_id'], incoming['u_id']))

@APP.route("/channel/removeowner/v1", methods=["POST"])
def channel_removeowner():
    ''' 
    Flask wrapper for channel_removeowner that takes a token 
    (of a Dreams/channel owner), channel_id and a user id, and 
    removes owner status from the specified user.
    '''
    incoming = request.get_json()
    channel_removeowner_v1(incoming['token'], incoming['channel_id'], \
                            incoming['u_id'])
    return saveAndReturn({})

@APP.route("/channel/leave/v1", methods=["POST"])
def channel_leave():
    ''' 
    Flask wrapper for channel_leave that takes a token and a 
    channel_id and removes the given user from the given channel.
    '''
    incoming = request.get_json()
    return saveAndReturn(channel_leave_v1(incoming['token'], \
                        incoming['channel_id']))

@APP.route("/channels/list/v2", methods=["GET"])
def channel_list():
    ''' 
    Flask wrapper for channels_list that takes a token and returns 
    a dictionary with all the channels that the user is in.
    '''
    return dumps({
        'channels' : channels_list_v1(request.args.get('token'))
    })

@APP.route("/channels/listall/v2", methods=["GET"])
def channel_listall():
    ''' 
    Flask wrapper for channel_listall that takes a token and 
    returns a dictionary with all Dreams channels.
    '''
    return dumps({
        'channels' : channels_listall_v1(request.args.get('token'))
    })

@APP.route("/channels/create/v2", methods=["POST"])
def channel_create():
    ''' 
    Flask wrapper for dm_create that takes a token, channel name
    and boolean declaring channel status (public or private) and
    returns a dictionary with the new channel_id created.
    '''
    incoming = request.get_json()
    return saveAndReturn({
        "channel_id" : channels_create_v1(incoming['token'], incoming['name'], incoming['is_public'])
    })

###############################################################
#                    MESSAGE FLASK ROUTES                     #
###############################################################

@APP.route('/message/send/v2', methods=['POST'])
def channel_message_send():
    ''' 
    Flask wrapper for message_send_dm that takes a token, a 
    channel_id and a message that is sent to the specified channel.
    '''
    incoming = request.get_json()
    return saveAndReturn({
        "message_id" : message_send_v1(incoming['token'], incoming['channel_id'], \
                                        incoming['message'], True)
    })

@APP.route('/message/edit/v2', methods=['PUT'])
def ch_or_dm_message_edit():
    ''' 
    Flask wrapper for message_edit that takes a token and a 
    message_id, editing the specified message.
    '''
    incoming = request.get_json()
    message_edit_v1(incoming['token'], incoming['message_id'], incoming['message'])
    return saveAndReturn({})

@APP.route('/message/remove/v1', methods=['DELETE'])
def ch_or_dm_message_remove():
    ''' 
    Flask wrapper for message_remove that takes a token and a 
    message_id, removing the specified message from Dreams.
    '''
    incoming = request.get_json()
    message_remove_v1(incoming['token'], incoming['message_id'])
    return saveAndReturn({})

@APP.route('/message/share/v1', methods=['POST'])
def channel_message_share():
    ''' 
    Flask wrapper for message_share that takes a token, channel_id,
    dm_id, message_id and optional message. Shares the specified
    message to the specified dm/channel and returns the shared message
    id.
    '''
    incoming = request.get_json()
    return saveAndReturn({
        'shared_message_id' : message_share_v1(incoming['token'], incoming['og_message_id'], \
                                                incoming['message'], incoming['channel_id'], \
                                                incoming['dm_id'])
    })

@APP.route('/message/sendlater/v1', methods=['POST'])
def channel_message_send_later():
    '''
    Flask wrapper for message_sendlater that takes a token, a 
    channel_id and a message that is sent to the specified channel. It
    also takes an integer unix timestamp for when the message should be
    sent.
    '''
    incoming = request.get_json()
    return saveAndReturn({
        "message_id" : message_send_later_v1(incoming['token'], incoming['channel_id'], \
                                    incoming['message'], True, incoming['time_sent'])
    })

@APP.route('/message/react/v1', methods=['POST'])
def message_react():
    incoming = request.get_json()
    return saveAndReturn(message_react_v1(incoming['token'], \
        incoming['message_id'], \
        incoming['react_id']))

@APP.route('/message/unreact/v1', methods=['POST'])
def message_unreact():
    incoming = request.get_json()
    return saveAndReturn(message_unreact_v1(incoming['token'], \
        incoming['message_id'], \
        incoming['react_id']))

@APP.route('/message/pin/v1', methods=['POST'])
def message_pin():
    incoming = request.get_json()
    return saveAndReturn(message_pin_unpin_v1(incoming['token'], \
        incoming['message_id'], True))

@APP.route('/message/unpin/v1', methods=['POST'])
def message_unpin():
    incoming = request.get_json()
    return saveAndReturn(message_pin_unpin_v1(incoming['token'], \
        incoming['message_id'], False))

###############################################################
#                       DM FLASK ROUTES                       #
###############################################################

@APP.route('/message/senddm/v1', methods=['POST'])
def dm_message_send():
    ''' 
    Flask wrapper for message_send_dm that takes a token, a dm_id
    and a message that is sent to the specified dm.
    '''
    incoming = request.get_json()
    return saveAndReturn({
        "message_id" : message_send_v1(incoming['token'], incoming['dm_id'], \
                                        incoming['message'], False)
    })

@APP.route('/dm/details/v1', methods=['GET'])
def dm_details():
    ''' 
    Flask wrapper for dm_details that takes a token and a dm_id,
    returning the details of the specified dm (if the user is a
    member). 
    '''
    return dumps(dm_details_v1(request.args.get('token'), \
                    int(request.args.get('dm_id'))))

@APP.route('/dm/list/v1', methods=['GET'])
def dm_list():
    ''' 
    Flask wrapper for dm_list that takes a token and returns 
    a dictionary with all the dms that the user is in.
    '''
    return dumps({
        'dms' : dm_list_v1(request.args.get('token'))
    })

@APP.route('/dm/create/v1', methods=['POST'])
def dm_create():
    ''' 
    Flask wrapper for dm_create that takes a token and a list of
    u_ids and creates a dm with all users specified. Returns a
    dictionary holding the dm_id and the dm name.
    '''
    incoming = request.get_json()
    return saveAndReturn(dm_create_v1(incoming['token'], incoming['u_ids']))

@APP.route('/dm/remove/v1', methods=['DELETE'])
def dm_remove():
    ''' 
    Flask wrapper for dm_remove that takes a token and a dm_id and
    removes the dm specified. 
    '''
    incoming = request.get_json()
    return saveAndReturn(dm_remove_v1(incoming['token'], incoming['dm_id']))

@APP.route('/dm/leave/v1', methods=['POST'])
def dm_leave():
    ''' 
    Flask wrapper for dm_invite that takes a token and a dm_id and
    removes the given user from the given dm.
    '''
    incoming = request.get_json()
    return saveAndReturn(dm_leave_v1(incoming['token'], incoming['dm_id']))

@APP.route('/dm/invite/v1', methods=['POST'])
def dm_invite():
    ''' 
    Flask wrapper for dm_invite that takes a token, a dm_id and
    the user id of the user to invite to the given dm. 
    '''
    incoming = request.get_json()
    res = dm_invite_v1(incoming['token'], incoming['dm_id'], incoming['u_id'])
    return saveAndReturn(res)

@APP.route('/dm/messages/v1', methods=['GET'])
def dm_messages():
    ''' 
    Flask wrapper for dm_messages that takes a token, a dm_id and
    a start value, returning a list of up to 50 messages between 
    index "start" and "start + 50". Also returns the start value
    and end value (-1 if the oldest messages have been returned) 
    '''
    return dumps(dm_messages_v1(request.args.get('token'), \
                                    int(request.args.get('dm_id')), \
                                    int(request.args.get('start'))))

@APP.route('/message/sendlaterdm/v1', methods=['POST'])
def dm_message_send_later():
    '''
    Flask wrapper for message_sendlater that takes a token, a 
    dm_id and a message that is sent to the specified dm. It
    also takes an integer unix timestamp for when the message should be
    sent.
    '''
    incoming = request.get_json()
    return saveAndReturn({
        "message_id" : message_send_later_v1(incoming['token'], incoming['dm_id'], \
                                    incoming['message'], False, incoming['time_sent'])
    })
###############################################################
#                    USER(/S) FLASK ROUTES                    #
###############################################################

@APP.route("/users/all/v1", methods=['GET'])
def http_users_all_v1():
    ''' 
    Flask wrapper for users_all that takes a token and returns a
    dictionary with a list of all users and their profiles.
    '''
    return saveAndReturn(users_all_v1(request.args.get("token")))

@APP.route("/user/profile/v2", methods=['GET'])
def get_user_profile_v2():
    ''' 
    Flask wrapper for user_profile that takes a token and the user id
    of the profile that is to be returned.
    '''
    return saveAndReturn(user_profile_v2(request.args.get("token"), \
                            int(request.args.get('u_id'))))

@APP.route("/user/profile/setname/v2", methods=['PUT'])
def set_user_profile_name_v2():
    ''' 
    Flask wrapper for user_setname that takes a token and a name
    which is to replace the current username.
    '''
    incoming = request.get_json()
    return saveAndReturn(user_profile_setname_v2(incoming['token'], \
            incoming['name_first'], incoming['name_last']))

@APP.route("/user/profile/setemail/v2", methods=['PUT'])
def set_user_profile_email_v2():
    ''' 
    Flask wrapper for user_setemail that takes a token and an email
    which is to replace the current user email.
    '''
    incoming = request.get_json()
    return saveAndReturn(user_profile_setemail_v2(incoming['token'], \
                            incoming['email']))

@APP.route("/user/profile/sethandle/v1", methods=['PUT'])
def set_user_profile_handle():
    ''' 
    Flask wrapper for user_sethandle that takes a token and a handle string
    which is to replace the current user handle_str.
    '''
    incoming = request.get_json()
    return saveAndReturn(user_profile_sethandle_v2(incoming['token'], \
                            incoming['handle_str']))

###############################################################
#                      ADMIN FLASK ROUTES                     #
###############################################################

@APP.route("/admin/user/remove/v1", methods=["DELETE"])
def admin_remove():
    ''' 
    Flask wrapper for admin_user_remove function that takes a token
    and a user id to remove.
    '''
    incoming = request.get_json()
    return saveAndReturn(admin_user_remove_v1(incoming['token'], \
                            incoming['u_id']))

@APP.route("/admin/userpermission/change/v1", methods=['POST'])
def admin_change():
    ''' 
    Flask wrapper for admin_permission_change function that takes 
    a token for an authorised owner and changes the permission of
    a given user to new permissions described by the permission id. 
    '''
    incoming = request.get_json()
    return saveAndReturn(admin_userpermission_change_v1(incoming['token'], \
                            incoming['u_id'], incoming['permission_id']))

###############################################################
#                     SEARCH FLASK ROUTES                     #
###############################################################

@APP.route("/search/v2", methods=["GET"])
def search():
    ''' 
    Flask wrapper for search function that takes in a token and a
    query string and returns a collection of messages in all the
    channels/dms that the user has joined matching the query.
    '''
    return dumps({
        'messages' : search_v2(request.args.get('token'), \
            request.args.get('query_str'))
    })

###############################################################
#                    STANDUP(/S) FLASK ROUTES                    #
###############################################################
    
@APP.route('/standup/start/v1', methods=['POST'])
def standup_start():
    incoming = request.get_json()
    res = standup_start_v1(incoming['token'], int(incoming['channel_id']), float(incoming['length']))
    return saveAndReturn(res)

@APP.route('/standup/active/v1', methods=['GET'])
def standup_active():
    res = standup_active_v1(request.args.get('token'), int(request.args.get('channel_id')))
    return saveAndReturn(res)

@APP.route('/standup/send/v1', methods=['POST'])
def standup_send():
    incoming = request.get_json()
    res = standup_send_v1(incoming['token'], int(incoming['channel_id']), incoming['message'])
    return saveAndReturn(res)

###############################################################
#                      OTHER FLASK ROUTES                     #
###############################################################

@APP.route("/notifications/get/v1", methods=["GET"])
def notifications():
    ''' 
    Flask wrapper for notifications function that takes in a token
    and returns a dictionary with up to 20 notifications. 
    Notifications are sent for channel/dm invitations and message
    tags only.
    '''
    token = request.args.get('token')
    return dumps({
        'notifications' : get_notifications_v1(token)
    })

@APP.route("/clear/v1", methods=["DELETE"])
def clear():
    ''' 
    Flask wrapper for clear function that takes no parameters
    and returns an empty dictionary.
    '''
    return saveAndReturn(clear_v1())

###############################################################
#                      AUXILLARY FUNCTIONS                    #
###############################################################

def saveAndReturn(responseObject):
    db.save_db()
    return dumps(responseObject)

if __name__ == "__main__":
    APP.run(port=config.port) # Do not edit this port
