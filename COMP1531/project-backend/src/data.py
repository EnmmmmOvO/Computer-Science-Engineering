from json import loads, dumps

try:
    with open('usersdb.json', 'r') as FILE1:
        users = loads(FILE1.read())
    with open('channelsdb.json', 'r') as FILE2:
        channels = loads(FILE2.read())
    with open('dmsdb.json', 'r') as FILE3:
        dms = loads(FILE3.read())
except FileNotFoundError:
    users = {}
    channels = {}
    dms = {}

def get_users():
    global users
    return users

def get_channels():
    global channels
    return channels

def get_dms():
    global dms
    return dms

def save_users():
    with open('usersdb.json', 'w') as FILE1:
        FILE1.write(dumps(get_users()))

def save_channels():
    with open('channelsdb.json', 'w') as FILE2:
        FILE2.write(dumps(get_channels()))

def save_dms():
    with open('dmsdb.json', 'w') as FILE3:
        FILE3.write(dumps(get_dms()))

def save_db():
    global users
    save_users()
    save_channels()
    save_dms()

