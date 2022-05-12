'''
distance
'''

def longest_distance(elements):
    '''
    input
    '''
    result = {}
    longest_result = {}
    for index in range(0, len(elements), 1):
        item = elements[index]
        if item not in result:
            result[item] = [index]
        else:
            result[item].append(index)
    for (k, v) in result.items():
        if len(v) < 2:
            continue
        else:
            longest_result.update({k: v[-1] - v[0]})
    if longest_result:
        return sorted(longest_result.items(), key=lambda x: -x[1])[0][1]
    return 0
