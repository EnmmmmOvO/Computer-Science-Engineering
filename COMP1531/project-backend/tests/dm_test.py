'''
Tests for dm create, details, list, remove, lea
'''
import pytest

from src.auth import auth_register_v1
from src.dm import dm_create_v1, dm_details_v1, dm_list_v1, \
                    dm_remove_v1, dm_invite_v1, dm_leave_v1, \
                    dm_messages_v1
from src.error import InputError, AccessError
from src.other import clear_v1
from src.message import message_send_v1
from src.data import save_db
import time


@pytest.fixture
def setup():
    clear_v1()
    user1 = auth_register_v1('apple@com.au', 'password1', 'Steve', 'Jobs')
    user2 = auth_register_v1('banana@com.au', 'password2', 'Steven', 'Jacobs')
    user3 = auth_register_v1('cherry@com.au', 'password3', 'Sarah', 'Jane')
    dm1 = dm_create_v1(user1['token'], [user2['auth_user_id'], user3['auth_user_id']])
    time.sleep(0.001) # interval for helper.uniqid generation
    dm2 = dm_create_v1(user2['token'], [user3['auth_user_id']])
    return {
        'sample_user1': user1,
        'sample_user2': user2,
        'sample_user3': user3,
        'invalid_token': 'eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJzZXNzaW9uX2lkIjoxfQ.bd98kGm7nnfY0FFpDFY2afxbN59JddYQn0-ZP9rNVIg',
        'sample_dm1': dm1,
        'sample_dm2': dm2
    }


def test_dm_create_v1(setup):
    assert dm_create_v1(setup['sample_user1']['token'], [setup['sample_user3']['auth_user_id']])


def test_dm_create_v1_except(setup):
    with pytest.raises(AccessError):
        # invalid auth_user_id
        assert dm_create_v1(setup['invalid_token'], [setup['sample_user1']['auth_user_id']])
    with pytest.raises(InputError):
        # invalid u_ids
        assert dm_create_v1(setup['sample_user1']['token'], [0, setup['sample_user1']['auth_user_id']])

    
def test_dm_details_v1(setup):
    answer = {'name': setup['sample_dm1']['dm_name'], 'members': [setup['sample_user2']['auth_user_id'], setup['sample_user3']['auth_user_id']]}
    # creator access
    assert dm_details_v1(setup['sample_user1']['token'], setup['sample_dm1']['dm_id']) == answer
    # member access
    assert dm_details_v1(setup['sample_user2']['token'], setup['sample_dm1']['dm_id']) == answer


def test_dm_details_v1_except(setup):
    with pytest.raises(AccessError):
        # invalid auth_user_id
        assert dm_details_v1(setup['invalid_token'], setup['sample_dm1']['dm_id'])

    with pytest.raises(InputError):
        # invalid dm_id
        assert dm_details_v1(setup['sample_user1']['token'], 0)

    with pytest.raises(AccessError):
        # auth_user_id is not a member of dm_id
        assert dm_details_v1(setup['sample_user1']['token'], setup['sample_dm2']['dm_id'])
    


def test_dm_list_v1(setup):
    answer = [
        {
            'dm_id': setup['sample_dm1']['dm_id'],
            'name': setup['sample_dm1']['dm_name']
        },
        {
            'dm_id': setup['sample_dm2']['dm_id'],
            'name': setup['sample_dm2']['dm_name']
        },
    ]
    assert dm_list_v1(setup['sample_user3']['token']) == answer


def test_dm_list_v1_except(setup):
    with pytest.raises(AccessError):
        # invalid auth_user_id
        assert dm_list_v1(setup['invalid_token'])


def test_dm_leave_v1(setup):
    assert dm_leave_v1(setup['sample_user1']['token'], setup['sample_dm1']['dm_id']) == {}
    assert dm_leave_v1(setup['sample_user2']['token'], setup['sample_dm1']['dm_id']) == {}

def test_dm_leave_v1_except(setup):
    with pytest.raises(AccessError):
        dm_leave_v1(setup['invalid_token'], setup['sample_dm1']['dm_id'])
    with pytest.raises(AccessError):
        dm_leave_v1(setup['sample_user1']['token'], setup['sample_dm2']['dm_id'])
    with pytest.raises(InputError):
        dm_leave_v1(setup['sample_user1']['token'], 0)
    
def test_dm_remove_v1(setup):
    assert dm_remove_v1(setup['sample_user2']['token'], setup['sample_dm2']['dm_id']) == {}


def test_dm_remove_v1_except(setup):
    with pytest.raises(AccessError):
        # invalid auth_user_id
        assert dm_remove_v1(setup['invalid_token'], setup['sample_dm1']['dm_id'])
    with pytest.raises(InputError):
        # invalid dm_id
        assert dm_remove_v1(setup['sample_user1']['token'], 0)

    with pytest.raises(AccessError):
        # auth_user_id is not the creator of dm_id
        assert dm_remove_v1(setup['sample_user1']['token'], setup['sample_dm2']['dm_id'])

def test_dm_invite_v1(setup):

    # user 1 - dm1
    # user 1 - dm2
    # user 2 - dm3

    # test case: user 1 invites user 1 into dm 1
    assert dm_invite_v1(setup['sample_user1']['token'], setup['sample_dm1']['dm_id'], setup['sample_user1']['auth_user_id']) == {}
    # test case: user 1 invites user 2 into dm 1
    assert dm_invite_v1(setup['sample_user1']['token'], setup['sample_dm1']['dm_id'], setup['sample_user2']['auth_user_id']) == {}

    # test case: user 2 invites user 1 into dm 1
    assert dm_invite_v1(setup['sample_user2']['token'], setup['sample_dm1']['dm_id'], setup['sample_user1']['auth_user_id']) == {}

    # test case: user 2 invites user 2 into dm 1
    assert dm_invite_v1(setup['sample_user2']['token'], setup['sample_dm1']['dm_id'], setup['sample_user2']['auth_user_id']) == {}

    # test case: user 2 invites user 1 into dm 2
    assert dm_invite_v1(setup['sample_user2']['token'], setup['sample_dm2']['dm_id'], setup['sample_user1']['auth_user_id']) == {}

def test_dm_invite_v1_except(setup):
    
    with pytest.raises(AccessError):
        # test case: auth_user_id does not refer to a valid user
        dm_invite_v1(setup['invalid_token'], setup['sample_dm1']['dm_id'], setup['sample_user1']['auth_user_id'])
    with pytest.raises(AccessError):
        # test case: auth_user_id is not a member of dm with dm_id
        dm_invite_v1(setup['sample_user1']['token'], setup['sample_dm2']['dm_id'], setup['sample_user2']['auth_user_id'])

    with pytest.raises(InputError):
        # test case: dm_id does not refer to a valid dm 
        dm_invite_v1(setup['sample_user1']['token'], 0, setup['sample_user2']['auth_user_id'])
    with pytest.raises(InputError):
        # test case: u_id does not refer to a valid user
        dm_invite_v1(setup['sample_user1']['token'], setup['sample_dm1']['dm_id'], -1)


# Test dm_messages_v1

def test_user_invalid(setup):
    '''
    Tests for AccessError exception given an invalid auth_user_id.
    '''
    with pytest.raises(AccessError):
        # User does not exist
        assert dm_messages_v1(setup['invalid_token'], setup['sample_dm2']['dm_id'], 0)

def test_dm_invalid(setup):
    '''
    Tests for InputError exception given an invalid dm_id.
    '''
    with pytest.raises(InputError):
        # dm -1 do not exist
        assert dm_messages_v1(setup['sample_user1']['token'], -1, 0)
    with pytest.raises(InputError):
        # dm 10 does not exist
        assert dm_messages_v1(setup['sample_user1']['token'], 10, 0)

def test_dm_no_join_permissions(setup):
    '''
    Tests for AccessError exception if unauthorised user sends message from
    a dm.
    '''
    with pytest.raises(AccessError):
        # Sample User 1 is not a member of private dm 2
        assert dm_messages_v1(setup['sample_user1']['token'], setup['sample_dm2']['dm_id'], 0)

def test_dm_messages_invalid_start(setup):
    '''
    Tests for InputError exception if start value is negative or greater than
    total number of dm messages.
    '''
    # No messages currently in the dm
    with pytest.raises(InputError):
        # start is greater than the total number of messages in the dm
        assert dm_messages_v1(setup['sample_user1']['token'], setup['sample_dm1']['dm_id'], 10)
    with pytest.raises(InputError):
        # start < 0
        assert dm_messages_v1(setup['sample_user1']['token'], setup['sample_dm1']['dm_id'], -10)

def test_dm_messages_end_index(setup):
    '''
    Tests for change in end index to ensure that -1 is returned after oldest
    messages have been returned.
    '''
    # Send 120 messages to private dm and check end index
    i = 0
    while i < 120:
        assert message_send_v1(setup['sample_user1']['token'], setup['sample_dm1']['dm_id'], 'Hello', False)
        i += 1

    ret = dm_messages_v1(setup['sample_user1']['token'], setup['sample_dm1']['dm_id'], 0)
    assert ret['start'] == 0 and ret['end'] == 50
    ret = dm_messages_v1(setup['sample_user1']['token'], setup['sample_dm1']['dm_id'], 50)
    assert ret['start'] == 50 and ret['end'] == 100
    ret = dm_messages_v1(setup['sample_user1']['token'], setup['sample_dm1']['dm_id'], 100)
    assert ret['start'] == 100 and ret['end'] == -1

