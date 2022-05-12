def balanced(n):
    '''
    Given a positive number n, compute the set of all strings of length n, in any order, that only
    contain balanced brackets. For example:
    >>> balanced(6)
    {'((()))', '(()())', '(())()', '()(())', '()()()'}

    Note that, by definition, the only string of length 0 containing balanced brackets is the empty
    string.

    Params:
      n (int): The length of string we want

    Returns:
      (set of str): Each string in this set contains balanced brackets. In the event n is odd, this
      set is empty.

    Raises:
      ValueError: If n is negative
    '''
    pass