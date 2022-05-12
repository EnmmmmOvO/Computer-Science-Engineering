'''
dictionary
'''

def construct_dict(keys, values):
    '''
    input
    '''
    if len(keys) != len(values):
        raise ValueError
    res = {}
    for i in range(0, len(keys), 1):
        res.update({keys[i]: values[i]})
    return res
