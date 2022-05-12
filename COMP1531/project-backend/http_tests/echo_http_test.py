import pytest
import requests
import json
from src import config

def test_echo():
    '''
    A simple test to check echo
    '''
    resp = requests.get(config.url + 'echo', params={'data': 'hello'})
    assert resp.status_code == 200
    # assert json.loads(resp.text) == {'data': 'hello'}

