'''
Tests
'''
from brooms import send_message, get_messages, clear, get_users, add_user


def test_simple():
    '''
    test simple
    '''
    clear()
    add_user("Hayden")
    assert (get_users() == {"users": ["Hayden"]})
    add_user("Rob")
    assert (get_users() == {"users": ["Rob", "Hayden"]})
    send_message("Hayden", "Rob", "Hello!")
    send_message("Hayden", "Rob", "Goodbye!")
    assert get_messages() == {
        "messages": [
            {"from": "Hayden", "to": "Rob", "message": "Hello!"},
            {"from": "Hayden", "to": "Rob", "message": "Goodbye!"},
        ]
    }


# Write your tests here
def test_difficult():
    '''
    test difficult
    '''
    clear()
    add_user("Hayden")
    assert (get_users() == {"users": ["Hayden"]})
    try:
        add_user("Hayden")
    except Exception as e:
        assert isinstance(e, KeyError)
    try:
        send_message("Hayden", "Rob", "Hello!")
    except Exception as e:
        assert isinstance(e, KeyError)
    try:
        send_message("Rob", "Hayden", "Hello!")
    except Exception as e:
        assert isinstance(e, KeyError)
    add_user("Rob")
    assert (get_users() == {"users": ["Rob", "Hayden"]})
    send_message("Hayden", "Rob", "Hello!")
    send_message("Hayden", "Rob", "Goodbye!")
    assert get_messages() == {
        "messages": [
            {"from": "Hayden", "to": "Rob", "message": "Hello!"},
            {"from": "Hayden", "to": "Rob", "message": "Goodbye!"},
        ]
    }
