import pytest
import json

from src.auth import auth_register_v1, auth_login_v1
from src.error import InputError
from src.other import clear_v1

#Global safe informations
safe_email = 'iamhappy@unsw.org'
safe_password = 'abcdefg'
safe_name_first = 'Mathews'
safe_name_last = 'Andrew'

@pytest.fixture()
def setup():
    clear_v1()
    user1 = auth_register_v1('apple@com.au', 'password1', 'Steve', 'Jobs')
    user2 = auth_register_v1('banana@com.au', 'password2', 'Steven', 'Jacobs')
    user3 = auth_register_v1('mango@com.au', 'password3', 'Thomas', 'Black')
    return {
        'u1': user1, 
        'u2': user2, 
        'u3': user3,
    }

#auth_login_v1

def test_invalid_email():
#Email entered is not a valid email
    with pytest.raises(InputError):
        auth_login_v1('12345678@qq.com.au', safe_password)
    with pytest.raises(InputError):
        auth_login_v1('12345678@qqcom', safe_password)
    with pytest.raises(InputError):
        auth_login_v1('12345678qq.com', safe_password)
    with pytest.raises(InputError):
        auth_login_v1('12345678@@qq.com', safe_password)
    with pytest.raises(InputError):
        auth_login_v1('@qq.com', safe_password)
    with pytest.raises(InputError):
        auth_login_v1('', safe_password)
        
def test_no_user_email(setup):
#Email entered does not belong to a user
    with pytest.raises(InputError):
        auth_login_v1('nouseremail@qq.com', safe_password)
    
def test_incorrect_password(setup):
#Password is not correct
    with pytest.raises(InputError):
        auth_login_v1('apple@com.au', 'wrongpassword')
    with pytest.raises(InputError):
        auth_login_v1('banana@com.au', 'wrongpassword')
