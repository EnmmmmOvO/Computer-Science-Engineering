import pytest
import sys
sys.path.append('./src')

if __name__ == '__main__':
    pytest.main(['-s', '-vv', 'tests/channel_test.py'])
    pytest.main(['-s', '-vv', 'tests/channels_test.py'])
    pytest.main(['-s', '-vv', 'tests/channel_join_test.py'])
    pytest.main(['-s', '-vv', 'tests/channel_messages_test.py'])
    pytest.main(['-s', '-vv', 'tests/dm_test.py'])
    pytest.main(['-s', '-vv', 'tests/standup_test.py'])
    pytest.main(['-s', '-vv', 'http_tests/standup_http_test.py'])