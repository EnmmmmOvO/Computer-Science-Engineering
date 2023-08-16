#!/usr/bin/env python3
"""
sorting a list based on the values in a hash
"""

import random

DAY_LIST = "Sunday Monday Tuesday Wednesday Thursday Friday Saturday".split()
DAY_NUMBER = dict((day, number) for number, day in enumerate(DAY_LIST))


def random_day_of_week():
    return random.choice(DAY_LIST)


def sort_days0(day_list):
    return sorted(day_list, key=lambda day: DAY_NUMBER[day])


def sort_days1(day_list):
    return sorted(day_list, key=DAY_NUMBER.get)


if __name__ == "__main__":
    print(DAY_LIST)
    print(DAY_NUMBER)
    random_days = [random_day_of_week() for _ in range(7)]
    print(random_days)
    print(sorted(random_days))
    print(sort_days0(random_days))
    print(sort_days1(random_days))
