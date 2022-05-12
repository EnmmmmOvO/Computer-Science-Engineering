import pytest
import json

from src.auth import auth_register_v1
from src.error import InputError
from src.other import clear_v1
    
#Global safe informations
safe_email = 'iamhappy@unsw.org'
safe_password = 'abcdefg'
safe_name_first = 'Mathews'
safe_name_last = 'Andrew'

#auth_register_v1

#Email entered is not a valid email
def test_enter_invalid_email():
    with pytest.raises(InputError):
        auth_register_v1('12345678@qq.com.au', safe_password, safe_name_first, safe_name_last)
    with pytest.raises(InputError):
        auth_register_v1('12345678@qqcom', safe_password, safe_name_first, safe_name_last)
    with pytest.raises(InputError):
        auth_register_v1('12345678qq.com', safe_password, safe_name_first, safe_name_last)
    with pytest.raises(InputError):
        auth_register_v1('12345678@@qq.com', safe_password, safe_name_first, safe_name_last)
    with pytest.raises(InputError):
        auth_register_v1('@qq.com', safe_password, safe_name_first, safe_name_last)
    with pytest.raises(InputError):
        auth_register_v1('', safe_password, safe_name_first, safe_name_last)
        
#Email address is already being used by another
def test_exist_email():
    auth_register_v1('87654321@qq.com', safe_password, safe_name_first, safe_name_last)
    with pytest.raises(InputError):
        auth_register_v1('87654321@qq.com', safe_password, safe_name_first, safe_name_last)
            
#Password entered is less than 6 characters long
def test_passward_too_short():
    with pytest.raises(InputError):
        auth_register_v1(safe_email, '123', safe_name_first, safe_name_last)
    with pytest.raises(InputError):
        auth_register_v1(safe_email, '', safe_name_first, safe_name_last)
        
#name_first is not between 1 and 50 characters inclusively in length
def test_invalid_first_name():
    with pytest.raises(InputError):
        auth_register_v1(safe_email, safe_password, safe_name_last, 'This is a really really really looooooooooooooong first name')
    with pytest.raises(InputError):
        auth_register_v1(safe_email, safe_password, '', safe_name_last)
    
#name_last is not between 1 and 50 characters inclusively in length
def test_invalid_last_name():
    with pytest.raises(InputError):
        auth_register_v1(safe_email, safe_password, safe_name_last, 'This is a really really really looooooooooooooong last name')
    with pytest.raises(InputError):
        auth_register_v1(safe_email, safe_password, safe_name_last, '')

#return a new auth_user_id
def test_return_new_id():
    clear_v1()
    result = auth_register_v1(safe_email, safe_password, 'Chin', 'Tom')
    assert result['auth_user_id'] == 1
    result = auth_register_v1('orange@com.au', safe_password, 'Chin', 'Tom')
    assert result['auth_user_id'] == 2
    result = auth_register_v1('watermelon@com.au', safe_password, 'Looooooooooooooong', 'Name')
    assert result['auth_user_id'] == 3
