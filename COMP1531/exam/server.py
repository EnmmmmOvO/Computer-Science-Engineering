'''
The flask server wrapper

All endpoints return JSON as output.
All POST requests pass parameters through JSON instead of Form.
'''
from json import dumps

from flask import Flask
from flask import request

import brooms

APP = Flask(__name__)

'''
Endpoint: '/users'
Method: GET
Parameters: ()
Output: { "users": [ ... list of strings ... ] }

Returns a list of all the users as a list of strings.
'''


# Write this endpoint here
@APP.route("/users", methods=["GET"])
def get_users():
    '''
    post_users
    '''
    users = brooms.get_users()
    return dumps(users)


'''
Endpoint: '/users'
Method: POST
Parameters: ( name: string )
Output: {}

Adds a user to the room/broom.
'''


# Write the endpoint here
@APP.route("/users", methods=["POST"])
def post_users():
    '''
    post_users
    '''
    data = request.get_json()
    name = data["name"]
    brooms.add_user(name)
    return dumps({})


'''
Endpoint: '/message'
Method: GET
Parameters: ()
Output: { "messages": [ { "from" : string, "to" : string, "message" : string } ] }

Returns a list of all the messages sent, who they came from, and who they are going to.
'''


# Write the endpoint here
@APP.route("/message", methods=["GET"])
def get_message():
    '''
    get message
    '''
    data = brooms.get_messages()
    return dumps(data)


'''
Endpoint: '/message'
Method: POST
Parameters: (user_from: string, user_to: string, message: string)
Output: {}

Sends a message from user "user_from" to user "user_to". All three parameters are strings.
'''


# Write the endpoint here
@APP.route("/message", methods=["POST"])
def post_message():
    '''
    post message
    '''
    data = request.get_json()
    brooms.send_message(data["user_from"], data["user_to"], data["message"])
    return dumps({})


if __name__ == '__main__':
    APP.run(debug=True)
