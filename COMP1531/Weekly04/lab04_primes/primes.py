"""
primes
"""
import math

def factors(num):
    """
    input
    """
    if num <= 1 or num % 1 != 0:
        """
        num is integer and greater than 1
        """ 
        return False

    list = []

    while num % 2 == 0: 
        """
        when possible factor is 2
        """
        list.append(2)
        num = num / 2
        
 
    for i in range(3,int(num)): 
        """
        when possiblefactor is more than 2
        """
        

        while num % i== 0: 
            """
            divide until smallest unit of i is obtained
            """
            list.append(int(i))
            num = num / i 
            

    if num > 2: 
        """
        remaining single factor
        """
        list.append(int(num))
        
    return list
