## Lab05 - Exercise - Simple (2 points)

This exercise should be be worked on individually. It may be in your exam, so practice it.

In `simple.py`, complete the flask server to store a list of names using a global variable as a list. It should have routes:
 * POST /name/add
   * input { name: 'example' }
   * output { }
 * GET /names
   * input { }
   * output { names: [ 'example1', 'example2' ] }
 * DELETE /name/remove
   * input { name: 'example' }
   * output { }

For example, if the following was done:
 * POST request made to /names/add with data { name: 'Asus' }
 * POST request made to /names/add with data { name: 'Acer' }
 * POST request made to /names/add with data { name: 'Dell' }
 * GET request made to /names would return { names: [ 'Asus', 'Acer', 'Dell' ]}
 * DELETE request made to /names/remove with data { name: 'Dell' }
 * GET request made to /names would return { names: [ 'Asus', 'Acer' ]}

Do **NOT** change the port the server listens on. By listening on port 0, the server will listen on a free port each time it is run. This is necessary to avoid interference on shared systems like VLAB, the SSH login servers as well as your CI pipelines.

Use the `requests` library (see week 4 lectures) to write python-based tests for the flask server in a file `simple_test.py`. A fixture has been provided for you that starts the server and gets the correct URL for testing. See the example test for how you should use it.

Ensure your code is pylint compliant.
