import pytest

from src.user import convert_to_user_profile, users_all_v1, user_profile_v2, user_profile_setname_v2, user_profile_setemail_v2, user_profile_sethandle_v2
from src.auth import auth_register_v1, auth_login_v1
from src.error import InputError, AccessError
from src.other import clear_v1

#function to create a user and log in
def generate_user():
    user = auth_register_v1("validEmail@email.com", "password", "Hayden", "James")
    auth_login_v1("validEmail@email.com", "password")
    
    return user

#test for user profile 
def test_user_profile_v2():
    clear_v1()
    
    test_user = generate_user()
    
    profile = {
        'u_id': test_user['auth_user_id'],
        'email': "validEmail@email.com",
        'name_first': "Hayden",
        'name_last': "James",
        'handle_str': "haydenjames",
    }
    assert user_profile_v2(test_user['token'], test_user['auth_user_id']).get('user') == profile
    assert users_all_v1(test_user['token']) == {'users': [profile]}

#testing user set name
def test_user_profile_setname_v2():

    clear_v1()
    
    test_user = generate_user()
    
    user_profile_setname_v2(test_user['token'], "John", "Smith")
    profile = user_profile_v2(test_user['token'], test_user['auth_user_id']).get('user')
    
    assert profile['name_first'] == "John"
    assert profile['name_last'] == "Smith"
    
# def test_user_profile_v2_empty():

#     clear_v1()

#     test_user = generate_user()
    
#     profile = user_profile_v2(test_user['token'], None)
    
#     assert profile == {}


#test invalid input for first name is >50 characters
def test_user_profile_setname_v2_firstname_error():

    clear_v1()
    
    test_user = generate_user()
    
    with pytest.raises(InputError):
        user_profile_setname_v2(test_user['token'], "Chiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiicken", "Nug")

    
#test invalid input for first name if name is <1
def test_user_profile_setname_v2_firstname_error2():

    clear_v1()
    
    test_user = generate_user()
    
    with pytest.raises(InputError):
        user_profile_setname_v2(test_user['token'], "", "Nug")
    

#test invalid input for last name if name is >50 characters
def test_user_profile_setname_v2_lastname_error():

    clear_v1()
    
    test_user = generate_user()
    
    with pytest.raises(InputError):
        user_profile_setname_v2(test_user['token'],"Chicken", "Nuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuug")


#test invalid input for last name if name is <1 character
def test_user_profile_setname_v2_lastname_error2():

    clear_v1()
    
    test_user = generate_user()
    
    with pytest.raises(InputError):
        user_profile_setname_v2(test_user['token'], "Chicken", "")

    
#test user email function
def test_user_profile_setemail_v2():
    
    clear_v1()
    
    test_user = generate_user()
    
    user_profile_setemail_v2(test_user['token'], "testEmail@email.com")
    profile = user_profile_v2(test_user['token'], test_user['auth_user_id']).get('user')
    
    assert profile['email'] == "testEmail@email.com"

#test for invalid email input
def test_user_profile_setemail_v2_invalid():
    
    clear_v1()
    
    test_user = generate_user()
    
    with pytest.raises(InputError):
        user_profile_setemail_v2(test_user['token'], "invalid_incorrect_email@email.com")

#test for existing email error
def test_user_profile_setemail_v2_existingemail():
    
    clear_v1()
    
    test_user = generate_user()
    auth_register_v1("CheckEmail@email.com", "valid_password", "Chicken", "Nug")
    auth_login_v1("CheckEmail@email.com", "valid_password")
    
    with pytest.raises(InputError):
        user_profile_setemail_v2(test_user['token'], "CheckEmail@email.com")
    with pytest.raises(InputError):
        user_profile_setemail_v2(test_user['token'], ("Apple" * 60) + "@email.com")

#test for set handle function
def test_user_profile_sethandle_v2():

    clear_v1()
    
    test_user = generate_user()
    
    user_profile_sethandle_v2(test_user['token'], "handler")
    profile = user_profile_v2(test_user['token'], test_user['auth_user_id']).get('user')
    
    assert profile['handle_str'] == "handler"

#test for existing handle error and invalid handle errors
def test_user_profile_sethandle_v2_existing():

    clear_v1()
    
    test_user = generate_user()
    
    user_profile_sethandle_v2(test_user['token'], "HANDLEBAR")
    
    existing_user = auth_register_v1("NewEmail@email.com", "valid_password", "Chicken", "Nug")
    auth_login_v1("NewEmail@email.com", "valid_password")
    
    with pytest.raises(InputError):
        user_profile_sethandle_v2(existing_user['token'], "HANDLEBAR")
    with pytest.raises(InputError):
        user_profile_sethandle_v2(existing_user['token'], "")
    with pytest.raises(InputError):
        user_profile_sethandle_v2(existing_user['token'], "A")
    with pytest.raises(InputError):
        user_profile_sethandle_v2(existing_user['token'], "HANDLEBARHANDLEBARHANDLEBAR")
    
def test_single_user():

    clear_v1()
    
    test_user = generate_user()

    user_profile_sethandle_v2(test_user['token'], "haydenjames")

    clear_v1()
