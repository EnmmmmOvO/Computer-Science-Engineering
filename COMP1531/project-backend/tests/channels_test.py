'''
Import files for channels_test 
'''
import pytest
from src.error import InputError, AccessError
from src.channels import channels_create_v1, channels_list_v1, channels_listall_v1
from src.auth import auth_register_v1
from src.other import clear_v1
import time

@pytest.fixture
def setup():
    '''
    Initialises internal data of application and creates two users, two private channels
    and one public channel.
    '''
    clear_v1()
    user1 = auth_register_v1('apple@com.au', 'password1', 'Steve', 'Jobs')
    user2 = auth_register_v1('banana@com.au', 'password2', 'Steven', 'Jacobs')
    channel1 = channels_create_v1(user1['token'], 'channel1', False)
    time.sleep(0.001) # interval for helper.uniqid generation
    channel2 = channels_create_v1(user1['token'], 'channel2', True)
    time.sleep(0.001) # interval for helper.uniqid generation
    channel3 = channels_create_v1(user2['token'], 'channel3', False)
    return {
        'sample_user1' : user1['token'],
        'sample_user2' : user2['token'], 
        'private_channel' : {'id': channel1, 'name':'channel1'},
        'public_channel' : {'id': channel2, 'name':'channel2'},
        'private_channel2' : {'id': channel3, 'name':'channel3'},
    }

# channels_create_v1 test functions
def test_channels_create_v1(setup):
    #testing successful channel creation
    assert channels_create_v1(setup['sample_user2'], 'Steven Jacobs', True)
    
def test_channels_create_except(setup):
    
    #testing for name length
    with pytest.raises(InputError):
        assert channels_create_v1(setup['sample_user1'], 'Haydeeeeeeeeen Jamesssss', True) 
    #testing for valid u_id
    invalid_token1 = 'eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJzZXNzaW9uc19pZCI6MX0.VRz789P4O1iWpmqlZupD25REjznk5kB1ICLnPnQaTdI'
    with pytest.raises(AccessError):
        assert channels_create_v1(invalid_token1, 'Steve', False) 


####
######channel_list test functions 
####

def test_channels_list(setup):
    """Test for multiple created channels by multiple users 
    """

    assert channels_list_v1(setup['sample_user1']) == [
            {
                'channel_id': setup['private_channel']['id'],
                'name': setup['private_channel']['name'],
            },
            {
                'channel_id': setup['public_channel']['id'],
                'name': setup['public_channel']['name'],
            },
        ]

def test_channels_list_empty():
    '''
    Testing when channel list is empty
    '''
    clear_v1()
    #create a new user 
    u_id = auth_register_v1("Darth@Vader.com", "star_wars123", "Luke", "Skywalker")
    #As no channels have been created, empty list 
    assert channels_list_v1(u_id['token']) == []

####
## channel_list_all test 
####

def test_channels_listall(setup):
    '''
    channels_listall should return both Public and Private channels associated with user1 and user2 
    '''
    
    list_all_channels = channels_listall_v1(setup['sample_user1'])
    assert list_all_channels == [
            {
                'channel_id': setup['private_channel']['id'],
                'name': setup['private_channel']['name'],
            },
            {
                'channel_id': setup['public_channel']['id'],
                'name': setup['public_channel']['name'],
            },
            {
                'channel_id': setup['private_channel2']['id'],
                'name': setup['private_channel2']['name'],
            },
        ]


def test_channels_listall_empty():
    '''
    #Two users with no channels
    '''
    clear_v1()
    u_id1 = auth_register_v1('Darth@Vader.com', 'star_wars123', 'Luke', 'Skywalker')
    u_id2  = auth_register_v1('Ahsoka@Tano.com', 'jedis_empire12', 'Palpatine', 'Padme')

    empty_channels = []
    assert channels_listall_v1(u_id1['token']) == empty_channels and channels_listall_v1(u_id2['token']) == empty_channels
