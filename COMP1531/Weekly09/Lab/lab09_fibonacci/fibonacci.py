'''
fibonacci number 
'''

def generate(n):
    '''
    input the Quantity required of fibonacci number
    '''

    if n == 1:
        # when n = 1
        return [0]

    # define the first and second fibonacci number
    fibs = [0,1]
    i = 0
    for i in range(n - 2):
        fibs.append(fibs[-2] + fibs[-1])
    del i
    return fibs


if __name__ == '__main__':
    print(generate("hey"))
