months = [
    'January',
    'February',
    'March',
    'April',
    'May',
    'June',
    'July',
    'August',
    'September',
    'October',
    'November',
    'December'
]

ending = ['st', 'nd', 'rd'] + 17 * ['th'] + ['st', 'nd', 'rd'] + 7 * ['th'] + ['st']

year = input ('Year: ')
month = input ('Month: ')
day = input ('Day: ')

month_a = int(month)
day_a = int(day)

month_b = months[month_a - 1]
ending_b = ending[day_a - 1]

print(month_b + ' ' + day + ending_b + ', ' + year)
