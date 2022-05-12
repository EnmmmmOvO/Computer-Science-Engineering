'''
Simplify the code
'''

def drykiss(my_list):
    '''
     (min value, The first four values are multiplied, The last four values are multiplied)
    '''
    return (min(my_list), my_list[0] * my_list[1] * my_list[2] * my_list[3], my_list[1] * my_list[2] * my_list[3] * my_list[4])


if __name__ == '__main__':
    a = input("Enter a: ")
    a = int(a)
    b = input("Enter b: ")
    b = int(b)
    c = input("Enter c: ")
    c = int(c)
    d = input("Enter d: ")
    d = int(d)
    e = input("Enter e: ")
    e = int(e)
    my_list = [a, b, c, d, e]
    result = drykiss(my_list)
    print("Minimum: " + str(result[0]))
    print("Product of first 4 numbers: ")
    print(f"  {result[1]}")
    print("Product of last 4 numbers")
    print(f"  {result[2]}")
