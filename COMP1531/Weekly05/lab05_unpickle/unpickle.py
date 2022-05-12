'''
unpickle.py
'''
import pickle

def most_common():
    '''
    read data
    '''
    f = open('shapecolour.p', 'rb')
    data = pickle.load(f)
    
    #combine it as a new string and store it
    new = []
    for item in data:
        new.append(item['colour'] + ' ' + item['shape'])
        
    #find the string appeared most
    number = 0
    result = {'Colour': None,'Shape': None,}
    for item in new:
        if new.count(item) > number:
            number = new.count(item)
            x =item.split(' ')
            result = {'Colour': x[0],'Shape': x[1],}

    return result


