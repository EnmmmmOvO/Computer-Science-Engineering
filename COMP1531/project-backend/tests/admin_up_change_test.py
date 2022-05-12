import pytest
import jwt
import json

from src.auth import auth_login_v1, auth_register_v1
from src.admin import admin_userpermission_change_v1
from src.error import InputError, AccessError
from src.other import clear_v1

#Permission id
OWNER = 1
MEMBER = 2
#secret for token
SECRET = 'This is a very safe secret'
@pytest.fixture()
def setup():
    clear_v1()
    user1 = auth_register_v1('apple@com.au', 'password1', 'Steve', 'Jobs')
    user2 = auth_register_v1('banana@com.au', 'password2', 'Steven', 'Jacobs')
    return {'token1': user1['token'], 'token2': user2['token'],}

def test_invalid_token():
    '''
    Token passed is a invalid id
    '''
    with pytest.raises(AccessError):
        invalid_token1 = 'eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJzZXNzaW9uc19pZCI6MX0.VRz789P4O1iWpmqlZupD25REjznk5kB1ICLnPnQaTdI'
        admin_userpermission_change_v1(invalid_token1, 1, OWNER)

def test_invalid_u_id(setup):
    '''
    u_id is invalid
    '''
    with pytest.raises(InputError):
        admin_userpermission_change_v1(setup['token1'], -1, OWNER)

def test_invalid_permission_id(setup):
    '''
    Permission id is invalid
    '''
    with pytest.raises(InputError):
        admin_userpermission_change_v1(setup['token1'], 2, -1)
    with pytest.raises(InputError):
        admin_userpermission_change_v1(setup['token1'], 2, 'apple')
    with pytest.raises(InputError):
        admin_userpermission_change_v1(setup['token1'], 2, 123456)

def test_not_owner(setup):
    '''
    The authorised user is not an owner
    '''
    with pytest.raises(AccessError):
        admin_userpermission_change_v1(setup['token2'], 1, MEMBER)

def test_change(setup):
    '''
    User1 change permission id of user2
    '''
    assert admin_userpermission_change_v1(setup['token1'], 2, OWNER) == {}
    assert admin_userpermission_change_v1(setup['token2'], 1, MEMBER) == {}
