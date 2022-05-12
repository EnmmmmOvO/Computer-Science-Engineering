'''
cockroaches
'''

def decontaminate(filenames):
    '''
    input
    '''
    result = dict()
    for filename in filenames:
        with open(filename) as file_:
            data = file_.readlines()
        for item in data:
            item = item.rstrip("\r\n")
            if item not in result:
                result[item] = 1
            else:
                result[item] = result[item] + 1
    return result
