''' This is an generator function'''
def bad_interview():
    '''
    A generator that yields all numbers from 1 onward, but with some exceptions:
    * For numbers divisible by 3 it instead yields "Fizz"
    * For numbers divisible by 5 it instead yields "Buzz"
    * For numbers divisible by both 3 and 5 it instead yields "FizzBuzz"
    '''
    
    # The number is started from 1
    number = 1
    while True:
        if number % 15 == 0:
            yield "FizzBuzz"
        elif number % 3 == 0:
            yield "Fizz"
        elif number % 5 == 0:
            yield "Buzz"
        else:
            yield number

        number += 1
