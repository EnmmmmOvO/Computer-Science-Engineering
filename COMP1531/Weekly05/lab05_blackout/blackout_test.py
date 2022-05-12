import pytest
import re
from subprocess import Popen, PIPE
import signal
from time import sleep
import requests

# Use this fixture to get the URL of the server.
@pytest.fixture
def url():
    url_re = re.compile(r' \* Running on ([^ ]*)')
    server = Popen(["python3", "server.py"], stderr=PIPE, stdout=PIPE)
    line = server.stderr.readline()
    local_url = url_re.match(line.decode())
    if local_url:
        yield local_url.group(1)
        # Terminate the server
        server.send_signal(signal.SIGINT)
        waited = 0
        while server.poll() is None and waited < 5:
            sleep(0.1)
            waited += 0.1
        if server.poll() is None:
            server.kill()
    else:
        server.kill()
        raise Exception("Couldn't get URL from local server")

def test_url(url):
    '''
    # A simple sanity test to check that your server is set up properly
    '''
    assert url.startswith("http")

def check_blackouts(actual, expected):
    for city in range(len(actual)):
        assert actual[city][0] == expected[city][0]
        assert actual[city][1] >= expected[city][1] - 2 and actual[city][1] <= expected[city][1] + 2

def test_documentation(url):
    requests.post(url + '/city', json={'name': 'City1', 'theta': 2.827433388230814})
    requests.post(url + '/city', json={'name': 'City2', 'theta': 0.9424777960769379})
    requests.post(url + '/satellite', json={'height': 20183000.0, 'velocity': 3874.0, 'theta': 3.141592653589793})
    requests.post(url + '/satellite', json={'height': 5100000.0, 'velocity': 5000.0, 'theta': 0.2345})

    response = requests.get(url + '/simulate').json()
    sample = [('City1', 633), ('City2', 531)]
    cities = response['cities']

    check_blackouts(cities, sample)

def test_single_satellite(url):
    requests.post(url + '/city', json={'name': 'Vegas', 'theta': 1})
    requests.post(url + '/city', json={'name': 'Sydney', 'theta': 2.5})
    requests.post(url + '/satellite', json={'height': 20210000, 'velocity': 1000, 'theta': 3})

    response = requests.get(url + '/simulate').json()
    sample = [('Sydney', 1073), ('Vegas', 1307)]
    cities = response['cities']

def test_disco(url):
    requests.post(url + '/city', json={'name': 'city1', 'theta': 0})
    requests.post(url + '/city', json={'name': 'city2', 'theta': 2.0943951024})
    requests.post(url + '/city', json={'name': 'city3', 'theta': 4.1887902048})

    requests.post(url + '/satellite', json={'height': 10000000, 'velocity': 9000, 'theta': 0})
    requests.post(url + '/satellite', json={'height': 10000000, 'velocity': 9000, 'theta': 0.7853981634})
    requests.post(url + '/satellite', json={'height': 10000000, 'velocity': 9000, 'theta': 1.5707963268})
    requests.post(url + '/satellite', json={'height': 10000000, 'velocity': 9000, 'theta':  4.7123889804})

    response = requests.get(url + '/simulate').json()
    sample = [('city1', 194), ('city2', 169), ('city3', 193)]
    cities = response['cities']

    check_blackouts(cities, sample)

def test_no_satellites(url):
    requests.post(url + '/city', json={'name': 'Perth', 'theta': 2.617993878})
    requests.post(url + '/city', json={'name': 'Sydney', 'theta': 5.235987756})

    response = requests.get(url + '/simulate').json()
    sample = [('Perth', 1440), ('Sydney', 1440)]
    cities = response['cities']

    check_blackouts(cities, sample)

def test_stationary_satellite(url):
    requests.post(url + '/city', json={'name': 'Perth', 'theta': 0})
    requests.post(url + '/city', json={'name': 'Sydney', 'theta': 1.5707963268})
    requests.post(url + '/satellite', json={'height': 2021202012021, 'velocity': 0, 'theta': 0})

    response = requests.get(url + '/simulate').json()
    sample = [('Perth', 0), ('Sydney', 1440)]
    cities = response['cities']

    check_blackouts(cities, sample)
