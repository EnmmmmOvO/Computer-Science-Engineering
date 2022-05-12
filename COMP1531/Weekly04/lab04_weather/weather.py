"""
weather
"""
import datetime
import csv

def weather(date,name):
    """
    In weather.py complete function weather that takes in two arguments:

    A date in the format "DD-MM-YYYY"
    The name of a location e.g. "Albury"
    """
    Min = 0
    Max = 0
    mint = 0
    maxt = 0
    leep = -1
    flag = 0
    with open('input.txt') as f:
        for line in f:
            if leep < 0:
                leep += 1
            else:
                l = line.split(',')
                Min += float(l[2])
                Max += float(l[3])
                leep += 1
                tmp = l[0].split('-')
                day = '-'.join(tmp[::-1])
                if day == date and l[1].lower() == name:
                    flag = 1
                    mint = float(l[2])
                    maxt = float(l[3])
        Min = round(Min / leep,2)
        Max = round(Max / leep,2)
        mindiff = round((Min-mint),2)
        maxdiff = round((Max-maxt),2)
        if(flag != 1):
            return(None,None)
        else:
            return(mindiff,maxdiff)

if __name__ == "__main__":
    date = input("Enter date(DD-MM-YYYY): ")
    name = input("Enter location: ")
    a,b = weather(date,name.lower())
    print((a,b))