'''
datetime module to get the current year
'''
from datetime import datetime


class Student:
    '''
    input
    '''
    def __init__(self,firstName,lastName,birth_Year):
        # make the instance variables as private
        # so that they cannot be accessed directly
        # we make them private by appending with two underscores
        # for accessing the values of the isntance variable we provide accessor functions
        self.__name = firstName+" "+lastName
        self.__birth_year = birth_Year

    def getName(self):
        '''
        return all name
        '''
        return self.__name

    def getAge(self): 
        '''
        return years apart
        '''
        return datetime.now().year - self.__birth_year

if __name__ == '__main__':
    s = Student('Rob','Everest',1961)
    # find the current year using the below line of code
    current_year =datetime.now().year

    # use accessor functions to get the value of birth year
    years_old = current_year-s.getAge()
    # use accessor functions to get the value of name
    print('{} is {} old'.format(s.getName(),years_old))

