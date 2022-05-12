import pytest
import json

from src.auth import auth_logout_v1, auth_login_v1, auth_register_v1
from src.error import AccessError
from src.other import clear_v1
import src.helper as helper

@pytest.fixture()
def setup():
    clear_v1()
    user1 = auth_register_v1('apple@com.au', 'password1', 'Steve', 'Jobs')
    user2 = auth_register_v1('banana@com.au', 'password2', 'Steven', 'Jacobs')
    user3 = auth_register_v1('mango@com.au', 'password3', 'Thomas', 'Black')
    return {
        'u1': user1, 
        'u2': user2['token'], 
        'u3': user3['token'],
    }

def test_invalid_token():
    #Token passed is a invalid token
    with pytest.raises(AccessError):
        auth_logout_v1('eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJzZXNzaW9uX2lkIjoxfQ.bd98kGm7nnfY0FFpDFY2afxbN59JddYQn0-ZP9rNVIg')

def test_login_logout(setup):
    lo1 = auth_logout_v1(setup['u1']['token'])
    assert lo1['is_success'] == True
    lo1 = auth_login_v1('apple@com.au', 'password1')
    assert lo1['auth_user_id'] == setup['u1']['auth_user_id']

    #logout users
    lo1 = auth_logout_v1(lo1['token'])
    lo2 = auth_logout_v1(setup['u2'])
    assert lo1['is_success'] == True
    assert lo2['is_success'] == True
